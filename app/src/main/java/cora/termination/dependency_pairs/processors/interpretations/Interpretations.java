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

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;
import java.util.Vector;

import charlie.smt.Addition;
import charlie.smt.CMult;
import charlie.smt.IVar;
import charlie.smt.IntegerExpression;
import charlie.smt.Multiplication;
import charlie.smt.SmtFactory;
import charlie.smt.SmtProblem;
import charlie.terms.FunctionSymbol;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.util.Pair;

public class Interpretations {

  /**
   * Recursively compute the cost of a term.
   * 
   * @param term                       The term to interpret.
   * @param problem                    The SMT problem to which variables will be
   *                                   added.
   * @param symbolArgumentWeights      The mapping of function symbols to their
   *                                   argument weights.
   * @param variableIntegerExpressions The mapping of variables to their
   *                                   IntegerExpressions.
   * 
   * @return The IntegerExpression representing the cost of the term.
   */
  public static IntegerExpression interpretTerm(
    Term term,
    SmtProblem problem,
    Hashtable<FunctionSymbol, Vector<IntegerExpression>> symbolArgumentWeights,
    Hashtable<Variable, IVar> variableIntegerExpressions) {

    if (term.isVariable()) { // Term root is a free (unsatisfied) variable
      variableIntegerExpressions.putIfAbsent(
        term.queryVariable(),
        SmtFactory.createIntegerVariable(problem, term.queryVariable().queryName(), 0, 10)
      );

      // return variable's associated cost expression
      return variableIntegerExpressions.get(term.queryVariable());
    }

    // Term is a function term.
    Vector<IntegerExpression> argumentWeights = symbolArgumentWeights.get(term.queryRoot());

    List<IntegerExpression> subtermCosts = new ArrayList<>(argumentWeights.size());
    subtermCosts.add(argumentWeights.getFirst()); // constant term

    for (int i = 0; i < term.numberArguments(); i++) {
      IntegerExpression innerExpression = interpretTerm(
        term.queryArguments().get(i), problem,
        symbolArgumentWeights, variableIntegerExpressions
      );

      subtermCosts.add(SmtFactory.createMultiplication(argumentWeights.get(i + 1), innerExpression));
    }

    // simplify the addition of all subterm costs and return,
    // if a term is simplified any later simplification calls will be constant time.
    return SmtFactory.createAddition(subtermCosts).simplify();
  }

  /**
   * Adds a coefficient expression to the list of coefficients for a variable
   * expression.
   * 
   * @param variableCoefficients The hashtable mapping variable expressions to
   *                             their coefficient lists.
   * @param coefficientExpr      The coefficient expression to add.
   * @param variableExpr         The variable expression to which the coefficient
   *                             belongs.
   */
  public static void addCoefficientToVarList(
    Hashtable<IntegerExpression, List<IntegerExpression>> variableCoefficients,
    IntegerExpression coefficientExpr,
    IntegerExpression variableExpr
  ) {
    variableCoefficients.putIfAbsent(variableExpr, new ArrayList<IntegerExpression>());
    variableCoefficients.get(variableExpr).add(coefficientExpr);
  }

  /**
   * Helper function for splitting a multiplication into variable and non-variable
   * parts.
   * 
   * @param multiplication
   * @param nonVariablesInChildExpressionOut
   * @param variableInChildExpressionOut
   * @param variableIntegerExpressions
   */
  public static void splitMultiplicationOnVariables(
    Multiplication multiplication,
    List<IntegerExpression> nonVariablesInChildExpressionOut,
    List<IntegerExpression> variableInChildExpressionOut,
    Hashtable<Variable, IVar> variableIntegerExpressions
  ) {
    for (int multChild = 1; multChild <= multiplication.numChildren(); multChild++) {
      IntegerExpression multiplicationChild = multiplication.queryChild(multChild);
      if (variableIntegerExpressions.containsValue(multiplicationChild)) {
        variableInChildExpressionOut.add(multiplicationChild);
      } else {
        nonVariablesInChildExpressionOut.add(multiplicationChild);
      }
    }
  }

  /**
   * TODO: Maybe this should be moved to IntegerExpression, or specifically to Addition.
   *       Would be named something like "factorOut" or "factorOutVariables".
   * 
   * A helper function for using absolute positiveness in tuple interpretations.
   * Splits an addition into a list of IntegerExpressions that do not contain
   * variables.
   * e.g. for an addition c + abXY + dY, where XY and Y are variables in
   * variableIntegerExpressions,
   * this method will return the list [c, ab, d].
   * 
   * @param addition                   The addition to split.
   * @param variableIntegerExpressions The mapping of variables to
   *                                   IntegerExpressions.
   * @return A list of IntegerExpressions that do not contain variables.
   */
  public static void combineTermsOnVariables(
    Addition addition,
    Hashtable<Variable, IVar> variableIntegerExpressions,
    Hashtable<IntegerExpression, List<IntegerExpression>> variableCoefficients
  ) {
    IntegerExpression multIdentity = SmtFactory.createValue(1);

    for (int childIndex = 1; childIndex <= addition.numChildren(); childIndex++) {
      IntegerExpression child = addition.queryChild(childIndex);

      switch (child) {
        case IVar var: // single variable
          if (variableIntegerExpressions.containsValue(var)) {
            // add 1 as coefficient to variable's coefficient list
            addCoefficientToVarList(variableCoefficients, multIdentity, var);
          } else {
            // add constant as part of the constant part
            addCoefficientToVarList(variableCoefficients, var, multIdentity);
          }
          break;

        case CMult cMult: // multiplication by a constant may also be a negated term
          if (cMult.queryChild() instanceof Multiplication mult) {
            // cMult is a wrapped multiplication
            List<IntegerExpression> nonVariables = new ArrayList<>();
            List<IntegerExpression> variables = new ArrayList<>();
            splitMultiplicationOnVariables(mult, nonVariables, variables, variableIntegerExpressions);

            // if mult has no variables (e.g. -(C0 * C1)), add to constant part
            if (variables.size() == 0) {
              addCoefficientToVarList(variableCoefficients, child, multIdentity);
              break;
            }

            // if mult has variables (e.g. -(C * V)), add coefficient (-C) to variable V's
            // list
            addCoefficientToVarList(variableCoefficients,
              SmtFactory.createMultiplication(
                cMult.queryConstant(),
                SmtFactory.createMultiplication(nonVariables)
              ).simplify(),
              SmtFactory.createMultiplication(variables)
            );
          } else {
            // cMult is a simple multiplication on a constant (e.g. -cC),
            // so we add it to the constant part
            if (!variableIntegerExpressions.containsValue(cMult.queryChild())) {
              addCoefficientToVarList(variableCoefficients, cMult, multIdentity);
              break;
            }

            // cMult is a multiplication on a variable (i.e. cV),
            // so we add the integer c to V's coefficient list
            addCoefficientToVarList(variableCoefficients,
              SmtFactory.createValue(cMult.queryConstant()),
              cMult.queryChild()
            );
          }
          break;

        case Multiplication mult:
          List<IntegerExpression> nonVariables = new ArrayList<>();
          List<IntegerExpression> variables = new ArrayList<>();
          splitMultiplicationOnVariables(mult, nonVariables, variables, variableIntegerExpressions);

          if (variables.size() == 0) {
            addCoefficientToVarList(variableCoefficients, child, multIdentity);
            break;
          }

          addCoefficientToVarList(variableCoefficients,
            SmtFactory.createMultiplication(nonVariables),
            SmtFactory.createMultiplication(variables)
          );
          break;

        default:
          throw new IllegalStateException("Unexpected child type in combineTermsOnVariables: " + child.getClass());
      }
    }
  }

  /**
   * Creates a simplified interpretation for a rule lhs -> rhs as an Addition
   * represented as: lhsCost - rhsCost in a simplified form.
   * 
   * @param lhs The left hand side term of the rule.
   * @param rhs The right hand side term of the rule.
   * @param problem The SMT problem to which variables will be added.
   * @param symbolArgumentWeights The mapping of function symbols to their argument weights.
   * @param variableIntegerExpressions The mapping of variables to their IntegerExpressions.
   * 
   * @return Simplified addition representing lhsCost - rhsCost
   */
  public static Pair<IntegerExpression, IntegerExpression> simplifiedIterpertationForRule(
    Term lhs, Term rhs,
    SmtProblem problem, 
    Hashtable<FunctionSymbol, Vector<IntegerExpression>> symbolArgumentWeights,
    Hashtable<Variable, IVar> variableIntegerExpressions
  ) {
    IntegerExpression lhsCost = interpretTerm(
      lhs, problem, symbolArgumentWeights, variableIntegerExpressions
    );

    IntegerExpression rhsCost = interpretTerm(
      rhs, problem, symbolArgumentWeights, variableIntegerExpressions
    );

    // Create constraint that lhsCost >= rhsCost -> lhsCost - rhsCost >= 0
    return new Pair<IntegerExpression, IntegerExpression>(lhsCost, rhsCost);
  }

}
