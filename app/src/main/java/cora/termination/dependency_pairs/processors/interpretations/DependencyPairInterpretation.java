package cora.termination.dependency_pairs.processors.interpretations;

import java.util.List;
import java.util.Map;

import charlie.smt.IVar;
import charlie.smt.IntegerExpression;
import charlie.smt.SmtFactory;
import charlie.smt.SmtProblem;
import cora.termination.dependency_pairs.DP;

public class DependencyPairInterpretation extends RuleInterpretation {
  private final IVar _reductionIndicator;
  
public DependencyPairInterpretation(DP dp, TermInterpreter interpreter, SmtProblem problem) {
    super(interpreter.interpret(List.of(dp.lhs(), dp.rhs())), null);
    
    _reductionIndicator = SmtFactory.createIntegerVariable(
      problem, dp.lhs().queryRoot() + "_red", 0, 1
    );
  }

  public IVar queryReductionIndicator() {
    return _reductionIndicator;
  }

  /**
   * Requires that the DP is weakly decreasing, modified by the strictness indicator.
   * If indicator = 0, constant part >= 1 (meaning strict decrease: Left - Right >= 1).
   * If indicator = 1, constant part >= 0 (meaning weak decrease: Left - Right >= 0).
   */
  @Override
  public void requireWeaklyDecreasing(SmtProblem problem) {
    Map<IntegerExpression, IntegerExpression> extracted = super.combineTermsOnParameterVariables();
    IntegerExpression oneKey = SmtFactory.createValue(1);

    extracted.forEach((variable, coefficient) -> {
      if (variable.equals(oneKey)) {
        // Adjust the constant part: Coeff + (-1 + Indicator) >= 0
        // Which simplifies to: Coeff >= 1 - Indicator
        IntegerExpression adjustment = SmtFactory.createAddition(
          SmtFactory.createValue(-1), 
          _reductionIndicator
        );
        IntegerExpression adjustedConstant = SmtFactory.createAddition(coefficient, adjustment).simplify();
        problem.require(SmtFactory.createGeq(adjustedConstant));
      } else {
        // Non-constant variable coefficients must simply remain absolute positive (>= 0)
        problem.require(SmtFactory.createGeq(coefficient));
      }
    });
  }
}