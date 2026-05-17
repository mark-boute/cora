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

import java.util.Hashtable;
import java.util.Set;

import charlie.smt.Constraint;
import charlie.smt.ConstraintPrinter;
import charlie.smt.IntegerExpression;
import charlie.smt.IExpPrinter;
import charlie.trs.Rule;
import charlie.util.Pair;
import charlie.terms.FunctionSymbol;
import cora.io.OutputModule;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;

public class PolynomialInterpretationProofObject extends ProcessorProofObject {

  private String _reason;
  private Boolean _success = false;
  private Hashtable<FunctionSymbol, IntegerExpression> _costFunctions;
  private Hashtable<Rule, Constraint> _ruleInterpretations;
  private Hashtable<DP, Pair<IntegerExpression, IntegerExpression>> _DPInterpretations;

  /**
   * A failed proof; SMT-Solver returned NO.
   * 
   * @param input
   */
  public PolynomialInterpretationProofObject(Problem input) {
    super(input);
  }

  /**
   * A MAYBE proof; SMT-Solver did not find a configuration to match the
   * constraints.
   * 
   * @param input
   * @param reason The reason returned by the SMT-Solver
   */
  public PolynomialInterpretationProofObject(Problem input, String reason) {
    super(input);
    _reason = reason;
  }

  /**
   * A successful proof; SMT-Solver returned SAT.
   * 
   * @param input         The input problem
   * @param oriented      The indexes of the oriented DPs
   * @param costFunctions The cost functions for each function symbol as
   *                      interpreted by the tuple interpretation
   */
  public PolynomialInterpretationProofObject(
      Problem input,
      Set<Integer> oriented,
      Hashtable<FunctionSymbol, IntegerExpression> costFunctions,
      Hashtable<Rule, Constraint> ruleInterpretations,
      Hashtable<DP, Pair<IntegerExpression, IntegerExpression>> DPInterpretations) {
    super(input, input.removeDPs(oriented, true));
    _success = oriented != null && !oriented.isEmpty();
    _costFunctions = costFunctions;
    _ruleInterpretations = ruleInterpretations;
    _DPInterpretations = DPInterpretations;
  }

  /**
   * Justifies the proof object by printing to the given output module.
   * 
   * @param module The output module to print to
   */
  @Override
  public void justify(OutputModule module) {

    IExpPrinter iExpPrinter = new IExpPrinter();
    ConstraintPrinter constraintPrinter = new ConstraintPrinter();

    if (!_success) {
      if (_reason == null) {
        module.println("No suitable tuple interpretation could be found.");
      } else {
        module.println("The SMT-Solver could not find a suitable tuple interpretation:\n" + _reason);
      }
      return;
    }
    module.println("A suitable tuple interpretation was found:");

    module.println("Cost functions for function symbols:");

    module.startTable();
    _costFunctions.forEach((term, expr) -> {
      module.nextColumn("J(%a)", term);
      module.nextColumn("=");
      module.println(iExpPrinter.print(expr));
    });

    module.endTable();

    module.println("Rule interpretations:");

    _ruleInterpretations.forEach((rule, constraint) -> {
      module.print("Rule '%a' was oriented using: ", rule);
      module.print("[[%a]] >= [[%a]]", rule.queryLeftSide(), rule.queryRightSide());
      module.println(", interpreted as %a", constraintPrinter.print(constraint));
    });

    if (!_output.isEmpty()) {
      module.println("Dependency Pair interpretations for non-oriented DPs:");

      _output.getFirst().getDPList().forEach(dp -> {
        module.print("Dependency pair '%a → %a' was oriented using:\n", dp.lhs(), dp.rhs());
        module.print("\t[[%a]] >= [[%a]]", dp.lhs(), dp.rhs());
        module.print(" with\n");
        module.println("\t%a >= %a", iExpPrinter.print(_DPInterpretations.get(dp).left()), iExpPrinter.print(_DPInterpretations.get(dp).right()));
      });

    }

    module.println("The following Dependency Pairs were oriented and have been removed from the problem.");

    _DPInterpretations.forEach((dp, expressionPair) -> {
      if (!_output.isEmpty() && _output.getFirst().getDPList().contains(dp)) return;

      module.print("Dependency pair '%a → %a' was strictly oriented using:\n", dp.lhs(), dp.rhs());
      module.print("\t[[%a]] > [[%a]]", dp.lhs(), dp.rhs());
      module.print(" with\n");
      module.println("\t%a > %a", iExpPrinter.print(expressionPair.left()), iExpPrinter.print(expressionPair.right()));
    });

    module.println("Done with run, next run:");

  }

  @Override
  public String queryProcessorName() {
    return "Polynomial Interpretation Processor";
  }
}
