package cora.termination.dependency_pairs.processors.interpretations;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import charlie.smt.Addition;
import charlie.smt.CMult;
import charlie.smt.IVar;
import charlie.smt.IntegerExpression;
import charlie.smt.Multiplication;
import charlie.smt.SmtFactory;
import charlie.smt.SmtProblem;
import charlie.trs.Rule;
import charlie.util.Pair;

public class RuleInterpretation {
  private final IntegerExpression _leftSideInterpretation;
  private final IntegerExpression _rightSideInterpretation;
  private final IntegerExpression _difference; // left - right, used for convenience
  private final List<IVar> _parameterVariables;

protected RuleInterpretation(Pair<List<IVar>, List<IntegerExpression>> interpretation, Rule rule) {
    _leftSideInterpretation = interpretation.right().get(0);
    _rightSideInterpretation = interpretation.right().get(1);
    _parameterVariables = interpretation.left();
    _difference = SmtFactory.createAddition(
      _leftSideInterpretation, 
      SmtFactory.createNegation(_rightSideInterpretation)
    ).simplify();
  }

  // Public constructor for standard Rules
  public RuleInterpretation(Rule rule, TermInterpreter interpreter) {
    this(interpreter.interpret(List.of(rule.queryLeftSide(), rule.queryRightSide())), rule);
  }

  public void requireWeaklyDecreasing(SmtProblem problem) {
    combineTermsOnParameterVariables().values().stream()
      .map(SmtFactory::createGeq)
      .forEach(problem::require);
  }

  public IntegerExpression queryLeftSideInterpretation() {
    return _leftSideInterpretation;
  }

  public IntegerExpression queryRightSideInterpretation() {
    return _rightSideInterpretation;
  }

  /**
   * A helper function for using absolute positiveness in tuple interpretations.
   * Splits an addition into a list of IntegerExpressions that do not contain
   * variables.
   * e.g. for an addition c + abXY + dY, where XY and Y are variables in
   * variableIntegerExpressions,
   * this method will return the map [1:c, XY:ab, Y:d].
   * @return A map from variable terms to their coefficient IntegerExpressions, and a separate entry for the constant part (with key multIdentity).
   */
  protected Map<IntegerExpression, IntegerExpression> combineTermsOnParameterVariables() {
    IntegerExpression one = SmtFactory.createValue(1);
    Map<IntegerExpression, IntegerExpression> coefficientsMap = new HashMap<>();

    List<IntegerExpression> children = (_difference instanceof Addition add) 
        ? IntStream.rangeClosed(1, add.numChildren()).mapToObj(add::queryChild).toList()
        : List.of(_difference);

    for (IntegerExpression child : children) {
      switch (child) {
        case IVar var: // single variable
          if (_parameterVariables.contains(var)) {
            // Add 1 to the variable's coefficient
            addCoefficient(coefficientsMap, var, one);
          } else {
            // Add the child to the constant part
            addCoefficient(coefficientsMap, one, child);
          }
          break;
        case CMult cMult:
          if (cMult.queryChild() instanceof Multiplication mult) {

            Pair<List<IntegerExpression>, List<IntegerExpression>> split = splitMultiplicationChildren(
              mult, _parameterVariables::contains
            );

            if (split.fst().isEmpty()) {
              addCoefficient(coefficientsMap, one, child);
            } else {
              // Prepend the outer CMult constant to the non-variable list
              split.snd().add(0, SmtFactory.createValue(cMult.queryConstant()));
              
              IntegerExpression combinedCoeff = SmtFactory.createMultiplication(split.snd()).simplify();
              IntegerExpression combinedVar = SmtFactory.createMultiplication(split.fst()).simplify();
              
              addCoefficient(coefficientsMap, combinedVar, combinedCoeff);
            }
          } else {
            IntegerExpression innerChild = cMult.queryChild();
            if (_parameterVariables.contains(innerChild)) {
              addCoefficient(coefficientsMap, innerChild, SmtFactory.createValue(cMult.queryConstant()));
            } else {
              addCoefficient(coefficientsMap, one, child);
            }
          }
          break;

        case Multiplication mult:

          Pair<List<IntegerExpression>, List<IntegerExpression>> split = splitMultiplicationChildren(
            mult, _parameterVariables::contains
          );

          if (split.fst().isEmpty()) {
            addCoefficient(coefficientsMap, one, child);
          } else {
            IntegerExpression combinedCoeff = SmtFactory.createMultiplication(split.snd()).simplify();
            IntegerExpression combinedVar = SmtFactory.createMultiplication(split.fst()).simplify();
            
            addCoefficient(coefficientsMap, combinedVar, combinedCoeff);
          }
          break;

        default:
          throw new IllegalStateException("Unexpected child type in combineTermsOnVariables: " + child.getClass());
      }
    }
  
    return coefficientsMap;
  }

  public Pair<IntegerExpression, IntegerExpression> substitution(Map<IVar, IntegerExpression> variableAssignments) {
    return new Pair<>(
      _leftSideInterpretation.substitute(variableAssignments).simplify(),
      _rightSideInterpretation.substitute(variableAssignments).simplify()
    );
  }

  private void addCoefficient(Map<IntegerExpression, IntegerExpression> map, IntegerExpression key, IntegerExpression valueToAdd) {
    map.compute(key, (k, existingCoeff) -> 
        (existingCoeff == null) 
            ? valueToAdd 
            : SmtFactory.createAddition(existingCoeff, valueToAdd).simplify()
    );
  }

  private Pair<List<IntegerExpression>, List<IntegerExpression>> splitMultiplicationChildren(
    Multiplication mult, 
    Predicate<IntegerExpression> condition
  ) {
    Map<Boolean, List<IntegerExpression>> partitioned = IntStream.rangeClosed(1, mult.numChildren())
      .mapToObj(mult::queryChild)
      .collect(Collectors.partitioningBy(condition));

    return new Pair<>(partitioned.get(true), partitioned.get(false));
  }
}
