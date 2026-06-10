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

// import java.util.HashMap;
import java.util.List;
import java.util.Map;
// import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import charlie.smt.*;
import charlie.terms.FunctionSymbol;
import charlie.trs.TrsProperties.Constrained;
import charlie.trs.TrsProperties.FreshRight;
import charlie.trs.TrsProperties.Level;
import charlie.trs.TrsProperties.Lhs;
import charlie.trs.TrsProperties.Root;
import charlie.trs.TrsProperties.TypeLevel;
import cora.config.Settings;
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

    TupleConfiguration config = TupleConfiguration.of(
        PolynomialConfiguration.of(PolynomialPart.CONSTANT, PolynomialPart.LINEAR),
        PolynomialConfiguration.of(PolynomialPart.CONSTANT, PolynomialPart.SQUARED)
        // PolynomialConfiguration.of(PolynomialPart.CONSTANT, PolynomialPart.INTERACTIONS)
        );

    Map<FunctionSymbol, SymbolTupleInterpretation> symbolTupleInterpretations = dpp.getOriginalTRS().queryAlphabet()
        .getSymbols().stream()
        .collect(Collectors.toMap(
            symbol -> symbol,
            symbol -> new SymbolTupleInterpretation.Builder(problem, symbol, config).build()));

    dpp.getOriginalTRS().queryRules().forEach(rule -> {
      RuleTupleInterpretation interpretation = new RuleTupleInterpretation(problem, rule, symbolTupleInterpretations);
      interpretation.requireWeaklyDecreasing();
    });

    return null;
  }

}
