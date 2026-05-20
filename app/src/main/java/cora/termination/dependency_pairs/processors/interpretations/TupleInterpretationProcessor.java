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

 package cora.termination.dependency_pairs.processors.interpretations;

// import java.util.HashMap;
import java.util.List;
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
// import cora.termination.dependency_pairs.DP;

public class TupleInterpretationProcessor implements Processor {

  private static final int TUPLE_SIZE = 2; 

  /**
   * Allow this processor to be disabled via settings.
   * 
   * @return The disabled code string.
   */
  public static String queryDisabledCode() {
    return "tupleinterp";
  }

  /**
   * Checks whether this processor is applicable to the given dependency pair problem.
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
        Root.FUNCTION, FreshRight.NONE
      );
  }

  /**
   * Processes a dependency pair problem using tuple interpretations.
   * 
   * @param dpp The dependency pair problem to process.
   * @return A proof object representing the result of the processing. 
   */
  @Override
  public ProcessorProofObject processDPP(Problem dpp) {

    // SmtProblem problem = new SmtProblem();

    // Instead of a single polynomial interpretation, we create a tuple of interpretations for each function symbol.
    // In order to combine this into a single SMT problem, we index the weight symbols.
    // Map<FunctionSymbol, List<SymbolInterpretation>> functionInterpretations = dpp.getOriginalTRS()
    //   .queryAlphabet().getSymbols().stream().collect(Collectors.toMap(
    //     symbol -> symbol,
    //     symbol -> this.createSymbolTupleInterpretation(symbol, problem)
    //   ));

    // With this tuple of IntegerExpressions, we can create a tuple of interpretations for each rule and DP, which we can then combine into a single SMT problem.

    // There are two distinctions we want to make between rules and DPs:
    // 1. For rules we require a non-increasing interpretation.
    // 2. For DPs we have two cases again: 
    //    a. Strictly decreasing interpretation, which is how we remove a DP from the problem.
    //    b. Non-increasing interpretation, which does not remove the DP, 
    //       but allows us to remove this DP in a later iteration of the framework.

    // For cases 1 and 2b we require: forall f in T: f >= 0.        
  
    // Store all the interpretations for the rules, so we can justify the proof object later.
    // Map<Rule, List<RuleInterpretation>> ruleInterpretations = dpp.getOriginalTRS()
    //   .queryRules().stream()
    //   .collect(Collectors.toMap(
    //     rule -> rule,
    //     rule -> IntStream.range(0, TUPLE_SIZE)
    //       .mapToObj(i -> new RuleInterpretation(rule, mapFunctionInterpretationsToIndex(functionInterpretations, i)))
    //       .collect(Collectors.toList())
    //   ));

    // For case 2a we require: f_0 > 0, and forall f_i with i > 0: f_i >= 0
    // We introduce an indicator variable for each DP, which is 0 if the DP is strictly decreasing, and 1 if the DP is non-increasing.
    // We then require that at least one DP is strictly decreasing, which ensures that we make progress towards termination.
    
        /*
       * for DPs we require at least >= 0, but in order to reduce towards termination
       * we need > 0.
       * We want to reduce as many DPs as possible in each step.
       * Therefor we try to find as many strictly decreasing DPs as possible,
       * in order to do this we rewrite forinstance a + bx + cy >= 0 to the form of:
       * a-d + bx + cy >= 0, which is equivalent to a + bx + cy > 0 iff d=1.
       * but SMT-s generaly try to stick to a value of 0, so we rewrite the constraint
       * to:
       * (a + 1 - d) + bx + cy, with for d=0 : `> 0`, and for d=1: `>= 0`,
       * making sure the SMT levetates towards strictly decreasing interpretations.
       */

    // Map<DP, IVar> dpIndicators = new HashMap<>();

    // dpp.getDPList().stream()
    //   .flatMap(dp -> interpretRule(dp.lhs(), dp.rhs(), functionInterpretations))
    //   .map(expr -> {
    //     IVar indicator = SmtFactory.createIntegerVariable(problem, dp.lhs().queryRoot() + "_red", 0, 1);
    //     dpIndicators.put(dp, indicator);
    //   }) // add indicator
    //   .forEach(problem::require);


    return null;
  }

  /** 
   * Helper function to create a tuple of SymbolInterpretations for a given function symbol, which we can then use to create interpretations for rules and DPs.
   * @param symbol The function symbol to create the interpretations for.
   * @param problem The SMT problem to create the integer variables in.
   * @return A tuple of SymbolInterpretations for the given function symbol.
   */
  // private List<SymbolInterpretation> createSymbolTupleInterpretation(FunctionSymbol symbol, SmtProblem problem) {
  //   return IntStream.range(0, TUPLE_SIZE)
  //     .mapToObj(i -> new SymbolInterpretation(problem, symbol, "t" + i + "_"))
  //     .collect(Collectors.toList());
  // }

  // private Map<FunctionSymbol, SymbolInterpretation> mapFunctionInterpretationsToIndex(
  //     Map<FunctionSymbol, List<SymbolInterpretation>> functionInterpretations, int index) {
    
  //   if (index < 0 || index >= TUPLE_SIZE) {
  //     throw new IllegalArgumentException("Index must be between 0 and " + (TUPLE_SIZE - 1));
  //   }
    
  //   return functionInterpretations.entrySet().stream()
  //     .collect(Collectors.toMap(
  //       Map.Entry::getKey,
  //       entry -> entry.getValue().get(index)
  //     ));
  // }
}
