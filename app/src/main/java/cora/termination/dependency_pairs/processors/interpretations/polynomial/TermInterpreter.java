package cora.termination.dependency_pairs.processors.interpretations.polynomial;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import charlie.smt.IVar;
import charlie.smt.IntegerExpression;
import charlie.smt.SmtFactory;
import charlie.smt.SmtProblem;
import charlie.terms.FunctionSymbol;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.util.Pair;

public class TermInterpreter {

  private final SmtProblem _problem;
  private final Map<FunctionSymbol, SymbolInterpretation> _functionInterpretations;
  private final List<IVar> _parameterVariableStore = new ArrayList<>();

  public TermInterpreter(SmtProblem problem, Map<FunctionSymbol, SymbolInterpretation> functionInterpretations) {
    _problem = problem;
    _functionInterpretations = functionInterpretations;
  }

  /**
   * Interpret a list of terms, sharing the same parameter variable map, and
   * return both the list of parameter variables and the list of interpretations.
   * This is useful for interpreting the left and right sides of a dependency pair
   * or rule together, to ensure that they share the same parameter variables.
   * 
   * @param terms
   * @return A pair of the list of parameter variables and the list of
   *         interpretations
   */
  public Pair<List<IVar>, List<IntegerExpression>> interpret(List<Term> terms) {
    Map<Variable, IVar> parameterVariableMap = new HashMap<>();

    List<IntegerExpression> interpretations = terms.stream()
        .map(term -> _interpret(term, parameterVariableMap))
        .toList();

    _parameterVariableStore.addAll(parameterVariableMap.values());
    return new Pair<>(parameterVariableMap.values().stream().toList(), interpretations);
  }

  public Pair<List<IVar>, IntegerExpression> interpret(Term term) {

    Map<Variable, IVar> _parameterVariableMap = new HashMap<>();
    IntegerExpression interpretation = _interpret(term, _parameterVariableMap);
    _parameterVariableStore.addAll(_parameterVariableMap.values());

    return new Pair<>(_parameterVariableMap.values().stream().toList(), interpretation);
  }

  private IntegerExpression _interpret(Term term, Map<Variable, IVar> parameterVariableMap) {
    if (term.isVariable()) { // Term root is a free (unsatisfied) parameter
      return parameterVariableMap.computeIfAbsent(
          term.queryVariable(),
          v -> SmtFactory.createIntegerVariable(_problem, v.queryName(), 0, 10));
    }

    // Term is a function symbol
    List<IntegerExpression> coefficients = _functionInterpretations.get(term.queryRoot()).getLinearCoefficients();
    List<IntegerExpression> subtermInterpretations = new ArrayList<>(coefficients.size());
    subtermInterpretations.addFirst(coefficients.getFirst());

    for (int i = 0; i < term.numberArguments(); i++) {
      subtermInterpretations.add(SmtFactory.createMultiplication(
          coefficients.get(i + 1), _interpret(term.queryArguments().get(i), parameterVariableMap)));
    }

    return SmtFactory.createAddition(subtermInterpretations).simplify();
  }
}
