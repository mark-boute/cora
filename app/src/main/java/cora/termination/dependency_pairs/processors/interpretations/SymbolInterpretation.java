package cora.termination.dependency_pairs.processors.interpretations;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import charlie.smt.IVar;
import charlie.smt.IntegerExpression;
import charlie.smt.SmtFactory;
import charlie.smt.SmtProblem;
import charlie.terms.FunctionSymbol;

public class SymbolInterpretation{
  
  private final FunctionSymbol _symbol;
  private final IntegerExpression _costFunction;
  private List<IntegerExpression> _coefficients = new ArrayList<>();

  /**
   * Creates a symbol interpretation for the given symbol and arity, 
   * using the given SMT problem to create the integer variables.  
   * The prefix is used to create unique variable names.
   * 
   * @param symbol The function symbol to interpret
   * @param problem The SMT problem used to create the integer variables
   * @param prefix A prefix for the variable names, to ensure uniqueness across different symbols, e.g. to distinguish between different indexes in a tuple.
   * 
   */
  public SymbolInterpretation(SmtProblem problem, FunctionSymbol symbol, String prefix) { 
    if (symbol == null) {
      throw new IllegalArgumentException("Symbol cannot be null");
    }
    if (symbol.queryName().isEmpty()) {
      throw new IllegalArgumentException("Symbols must have a name");
    }

    _symbol = symbol;
      
    // 1. Create the SMT variables for the coefficients
    _coefficients.add(SmtFactory.createIntegerVariable(problem, prefix + symbol.queryName() + "_c", 0, 10)); // Constant term
    for (int i = 0; i < symbol.queryArity(); i++) {
      _coefficients.add(SmtFactory.createIntegerVariable(problem, prefix + symbol.queryName() + "_s" + i, 0, 10));
    }

    // 2. Build the abstract structural cost function polynomial: c + s0*a + s1*b + ...
    List<IntegerExpression> subterms = new ArrayList<>();
    subterms.add(_coefficients.get(0)); // Start with the constant term 'c'
      
    for (int argIndex = 0; argIndex < symbol.queryArity(); argIndex++) {
      // Reconstruct the structural variable terms (e.g., 'a', 'b', 'c'...) for visual output
      IntegerExpression argVariable = SmtFactory.createIntegerVariable(
        problem, String.valueOf((char) ('a' + argIndex)), argIndex, argIndex
      );
      
      subterms.add(SmtFactory.createMultiplication(
        _coefficients.get(argIndex + 1),
        argVariable
      ));
    }
    _costFunction = SmtFactory.createAddition(subterms);
  }

  /**
   * Creates a symbol interpretation for the given symbol and arity, using the given SMT problem to create the integer variables.
   * 
   * @param symbol The function symbol to interpret
   * @param problem The SMT problem used to create the integer variables
   */
  public SymbolInterpretation(SmtProblem problem, FunctionSymbol symbol) {
    this(problem, symbol, "");
  }

  public IntegerExpression substitution(Map<IVar, IntegerExpression> variableAssignments) {
    return _costFunction.substitute(variableAssignments).simplify();
  }

  public FunctionSymbol querySymbol() {
    return _symbol;
  }

  public List<IntegerExpression> getCoefficients() {
    return _coefficients;
  }

  /**
   * Returns the generic polynomial cost expression for this symbol,
   * e.g., c + w_1 * a + w_2 * b
   */
  public IntegerExpression queryCostFunction() {
    return _costFunction;
  }
}
