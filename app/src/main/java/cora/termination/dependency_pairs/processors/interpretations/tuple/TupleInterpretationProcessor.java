/**************************************************************************************************
 Copyright 2026 Mark Boute

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.termination.dependency_pairs.processors.interpretations.tuple;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import charlie.smt.*;
import charlie.terms.FunctionSymbol;
import charlie.trs.Rule;
import charlie.smt.SmtSolver.Answer;
import charlie.trs.TrsProperties.Constrained;
import charlie.trs.TrsProperties.FreshRight;
import charlie.trs.TrsProperties.Level;
import charlie.trs.TrsProperties.Lhs;
import charlie.trs.TrsProperties.Root;
import charlie.trs.TrsProperties.TypeLevel;
import charlie.util.Pair;
import cora.config.Settings;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.processors.Processor;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;

public class TupleInterpretationProcessor implements Processor {

  /**
   * Allow this processor to be disabled via settings.
   * 
   * @return The disabled code string.
   */
  public static String queryDisabledCode() {
    return "tupleinterp";
  }

  /**
   * Checks whether this processor is applicable to the given dependency pair
   * problem.
   * 
   * @param dpp The dependency pair problem to check.
   * @return True if the processor is applicable, false otherwise.
   */
  @Override
  public boolean isApplicable(Problem dpp) {
    return !Settings.isDisabled(queryDisabledCode()) &&
        dpp.getOriginalTRS().verifyProperties(
            Level.FIRSTORDER, Constrained.NO,
            TypeLevel.SIMPLE, Lhs.PATTERN,
            Root.FUNCTION, FreshRight.NONE);
  }

  /**
   * Processes a dependency pair problem using tuple interpretations.
   * 
   * @param dpp The dependency pair problem to process.
   * @return A proof object representing the result of the processing.
   */
  @Override
  public ProcessorProofObject processDPP(Problem dpp) {

    SmtProblem problem = new SmtProblem();

    /**
     * Configure the shape of the tuple interpretations. Each function symbol will
     * be interpreted as a tuple of polynomials.
     * The length of the configuration determines the length of the tuple.
     * 
     * Any configuration may contain:
     * - A constant part, which is a non-negative integer.
     * - A linear part, which is a non-negative integer coefficient for each
     * argument of the function symbol.
     * - A squared part, which is a non-negative integer coefficient for the square
     * of each argument of the function symbol.
     * - A interaction part, which is a non-negative integer coefficient for the
     * product of any combination of two of the arguments of the function symbol.
     * 
     */
    TupleConfiguration config = TupleConfiguration.of(
        PolynomialConfiguration.of(PolynomialPart.CONSTANT, PolynomialPart.LINEAR),
        PolynomialConfiguration.of(PolynomialPart.CONSTANT, PolynomialPart.SQUARED)
    // PolynomialConfiguration.of(PolynomialPart.CONSTANT, PolynomialPart.LINEAR,
    // PolynomialPart.SQUARED)
    );

    /**
     * Create a tuple interpretation for each function symbol to reuse the
     * coefficients.
     * Each SymbolTupleInterpretation has a partial function which may be applied to
     * a subterm's interpretation.
     */
    Map<FunctionSymbol, SymbolTupleInterpretation> symbolTupleInterpretations = dpp.getOriginalTRS().queryAlphabet()
        .getSymbols().stream()
        .collect(Collectors.toMap(
            symbol -> symbol,
            symbol -> new SymbolTupleInterpretation.Builder(problem, symbol, config).build()));

    /**
     * Interpret each rule using the symbol tuple interpretations.
     * For each rule we require a weakly decreasing interpretation.
     * For each rule l -> r we require [[l]] >= [[r]], where l and r are tuples.
     * in order to have [[l]] >= [[r]] we require for each i in the tuple that
     * [[l]]_i >= [[r]]_i
     */
    Map<Rule, RuleTupleInterpretation> ruleTupleInterpretations = dpp.getOriginalTRS().queryRules().stream()
        .collect(Collectors.toMap(
            rule -> rule,
            rule -> new RuleTupleInterpretation(problem, rule, symbolTupleInterpretations)));
    ruleTupleInterpretations.values().forEach(RuleTupleInterpretation::requireWeaklyDecreasing);

    /**
     * Similarly, interpret each dependency pair using the symbol tuple
     * interpretations.
     * In the case of DPs we add a reduction indicator, so we may require a strict
     * decrease.
     * for each dp l -> r we require may [[l]] > [[r]], where l and r are tuples.
     * We do this by requiring [[l]]_0 >= [[r]]_0 + 1, where 1 is the value of the
     * reduction indicator.
     * For all other i in the tuple we require [[l]]_i >= [[r]]_i, so that the
     * reduction indicator only affects the first element of the tuple.
     */
    Map<DP, DPTupleInterpretation> dpTupleInterpretations = dpp.getDPList().stream()
        .collect(Collectors.toMap(
            dp -> dp,
            dp -> new DPTupleInterpretation(problem, dp, symbolTupleInterpretations),
            (existing, replacement) -> existing));
    dpTupleInterpretations.values().forEach(DPTupleInterpretation::requireWeaklyDecreasing);

    /**
     * Finally, we require that at least one of the dependency pairs is strictly
     * decreasing,
     * so that we can _progress_ towards termination.
     */
    problem.require(SmtFactory.createDisjunction(
        dpTupleInterpretations.values().stream()
            .map(dpTI -> SmtFactory.createGreater(dpTI.queryReductionIndicator()))
            .toList()));

    return switch (Settings.smtSolver.checkSatisfiability(problem)) {
      case Answer.YES(Valuation val) -> {

        Map<IVar, IntegerExpression> weightAssignments = symbolTupleInterpretations.values().stream()
            .flatMap(sti -> sti.queryCoefficients().stream())
            .flatMap(List::stream)
            .collect(Collectors.toMap(
                entry -> entry,
                entry -> SmtFactory.createValue(val.queryAssignment(entry))));

        dpTupleInterpretations.values()
            .forEach(dpTI -> dpTI.setOriented(val.queryAssignment(dpTI.queryReductionIndicator()) == 1));

        Set<DP> oriented = dpTupleInterpretations.entrySet().stream()
            .filter(entry -> entry.getValue().isOriented())
            .map(Map.Entry::getKey)
            .collect(Collectors.toSet());

        Map<FunctionSymbol, List<String>> symbolInterps = symbolTupleInterpretations.entrySet().stream()
            .collect(Collectors.toMap(
                Map.Entry::getKey,
                entry -> entry.getValue().toEvaluatedStrings(weightAssignments)));

        Map<Rule, Pair<List<String>, List<String>>> ruleInterps = ruleTupleInterpretations.entrySet().stream()
            .collect(Collectors.toMap(
                Map.Entry::getKey,
                entry -> entry.getValue().toEvaluatedStrings(weightAssignments)));

        // Set each reduction indicator to 0 for printing.
        dpTupleInterpretations.values().stream()
            .map(DPTupleInterpretation::queryReductionIndicator)
            .forEach(reductionIndicator -> weightAssignments.put(reductionIndicator, SmtFactory.createValue(0)));

        Map<DP, Pair<List<String>, List<String>>> dpInterps = dpTupleInterpretations.entrySet().stream()
            .collect(Collectors.toMap(
                Map.Entry::getKey,
                entry -> entry.getValue().toEvaluatedStrings(weightAssignments)));

        yield new TupleInterpretationProofObject(dpp, oriented, symbolInterps, ruleInterps, dpInterps);
      }

      case Answer.MAYBE(String reason) -> {
        yield new TupleInterpretationProofObject(dpp, reason);
      }

      case Answer.NO() -> {
        yield new TupleInterpretationProofObject(dpp);
      }
    };
  }

}
