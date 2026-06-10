package cora.termination.dependency_pairs.processors.interpretations.polynomial;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import charlie.smt.IVar;
import charlie.smt.IntegerExpression;
import charlie.smt.SmtFactory;
import charlie.smt.SmtProblem;
import charlie.terms.FunctionSymbol;

public class SymbolInterpretation{
  
  private final SmtProblem _problem;
  private final FunctionSymbol _symbol;
  private final String _coefficientPrefix;

  private final IVar _constantTerm;

  private final List<IVar> _argumentVariables = new ArrayList<>();

  private final IntegerExpression _linearTerms;
  private final List<IntegerExpression> _linearCoefficients = new ArrayList<>();

  private IntegerExpression _quadraticTerms;
  private final List<IntegerExpression> _quadraticCoefficients = new ArrayList<>();

  private IntegerExpression _interactionTerms;
  private final List<IntegerExpression> _interactionCoefficients = new ArrayList<>();

  /**
   * Creates a symbol interpretation for the given symbol and arity, 
   * using the given SMT problem to create the integer variables.  
   * The prefix is used to create unique variable names.
   * 
   * @param symbol The function symbol to interpret
   * @param problem The SMT problem used to create the integer variables
   * @param coefficient_prefix A prefix for the coefficient names, to ensure uniqueness across different symbols, e.g. to distinguish between different indexes in a tuple.
   * 
   */
  public SymbolInterpretation(SmtProblem problem, FunctionSymbol symbol, String coefficientPrefix) { 
    if (symbol == null) {
      throw new IllegalArgumentException("Symbol cannot be null");
    }
    if (symbol.queryName().isEmpty()) {
      throw new IllegalArgumentException("Symbols must have a name");
    }

    _problem = problem;
    _symbol = symbol;
    _coefficientPrefix = coefficientPrefix;

    // 1. Create the SMT variables for the coefficients
    _constantTerm = SmtFactory.createIntegerVariable(problem, coefficientPrefix + symbol.queryName() + "_c", 0, 10);

    // 2. Build linear section of the cost function: c1*x1 + c2*x2 + ...
    List<IntegerExpression> subterms = new ArrayList<>();      
    for (int argIndex = 1; argIndex <= symbol.queryArity(); argIndex++) {

      IVar coefficient = SmtFactory.createIntegerVariable(problem, coefficientPrefix + symbol.queryName() + "_c" + argIndex, 0, 10);
      _linearCoefficients.add(coefficient);

      // Reconstruct the parameter variable for visualizing this argument, e.g., x1, x2, etc.
      IVar argVariable = SmtFactory.createIntegerVariable(
        problem, "x" + String.valueOf(argIndex), 0, 1
      );
      _argumentVariables.add(argVariable);

      subterms.add(SmtFactory.createMultiplication(
        coefficient,
        argVariable
      ));
    }
    _linearTerms = SmtFactory.createAddition(subterms).simplify();
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

  /**
   * Returns the symbol that is being interpreted.
   * 
   * @return The symbol that is being interpreted
   */
  public FunctionSymbol querySymbol() {
    return _symbol;
  }

  public IntegerExpression getConstantTerm() {
    return _constantTerm;
  }

  public IntegerExpression getLinearTerms() {
    return _linearTerms;
  }

  public List<IntegerExpression> getLinearCoefficients() {
    return Stream
      .concat(Stream.of(_constantTerm), _linearCoefficients.stream())
      .collect(Collectors.toList());
  }

  private void generateQuadraticTerms() {
    List<IntegerExpression> subterms = new ArrayList<>();      
    // For each argument, create a quadratic term of the form cqi * xi^2
    for (int argIndex = 1; argIndex <= _symbol.queryArity(); argIndex++) {

      IVar coefficient = SmtFactory.createIntegerVariable(_problem, _coefficientPrefix + _symbol.queryName() + "_cq" + argIndex, 0, 10);
      _quadraticCoefficients.add(coefficient);

      IntegerExpression argVariable = _argumentVariables.get(argIndex - 1);
    
      subterms.add(SmtFactory.createMultiplication(
        coefficient,
        SmtFactory.createMultiplication(argVariable, argVariable).simplify()
      ));
    }
    _quadraticTerms = SmtFactory.createAddition(subterms);
  }

  public IntegerExpression getQuadraticTerms() {
    if (_quadraticTerms != null) generateQuadraticTerms();
    return _quadraticTerms;
  }

  public List<IntegerExpression> getQuadraticCoefficients() {
    if (_quadraticTerms != null) generateQuadraticTerms();
    return _quadraticCoefficients;
  }

  private <T> List<List<T>> getFilteredPowerset(List<T> list, int minSize, int maxSize) {
    List<List<T>> result = new ArrayList<>();
    int n = list.size();
    int totalCombinations = 1 << n; // 2^n total combinations

    for (int i = 0; i < totalCombinations; i++) {
      if (minSize <= Integer.bitCount(i) && Integer.bitCount(i) <= maxSize) {
        List<T> currentCombination = new ArrayList<>();
        for (int j = 0; j < n; j++) {
          if ((i & (1 << j)) != 0) currentCombination.add(list.get(j));
        }
        result.add(currentCombination);
      }
    }
    return result;
  }

  private void generateInteractionTerms() {
    List<IntegerExpression> subterms = new ArrayList<>();
    
    // Get all combinations of indices for the arguments, of size 2
    // (e.g., for arity 3: [1,2], [1,3], [2,3],
    //  explicitly leaving out [1,2,3] (cubic) and [1], [2], [3] (linear) )
    List<List<Integer>> combinations = getFilteredPowerset(
        IntStream.rangeClosed(1, _symbol.queryArity()).boxed().toList(), 
        2, 2
    );

    // For each combination, create an interaction term of the form ci1_2 * x1 * x2 (for combination [1,2]), 
    // ci1_3 * x1 * x3 (for combination [1,3]), etc.
    for (List<Integer> combination : combinations) {
      
      // Build a unique name suffix based on indices involved: e.g., "_ci1_2" or "_ci1_2_3"
      StringBuilder nameBuilder = new StringBuilder(_coefficientPrefix + _symbol.queryName() + "_ci");
      combination.forEach(index -> nameBuilder.append("_").append(index));
      
      IVar coefficient = SmtFactory.createIntegerVariable(_problem, nameBuilder.toString(), 0, 10);
      _interactionCoefficients.add(coefficient);

      // create the interaction term by multiplying the coefficient with the involved variables, e.g., ci1_2 * x1 * x2
      List<IntegerExpression> multiplicationArgs = new ArrayList<>();
      multiplicationArgs.add(coefficient);

      combination.stream()
        .map(index -> _argumentVariables.get(index - 1))
        .forEach(multiplicationArgs::add);

      subterms.add(SmtFactory.createMultiplication(multiplicationArgs).simplify());
    }
    
    _interactionTerms = SmtFactory.createAddition(subterms);
  }

  public IntegerExpression getInteractionTerms() {
    if (_interactionTerms != null) generateInteractionTerms();
    return _interactionTerms;
  }

  public List<IntegerExpression> getInteractionCoefficients() {
    if (_interactionTerms != null) generateInteractionTerms();
    return _interactionCoefficients;
  }

  /**
   * Returns the generic linear cost expression for this symbol,
   * e.g., c + w_1 * a + w_2 * b
   */
  public IntegerExpression queryLinearCostFunction() {
    return SmtFactory.createAddition(_constantTerm, _linearTerms);
  }

  public IntegerExpression queryQuadraticCostFunction() {
    return SmtFactory.createAddition(this.queryLinearCostFunction(), getQuadraticTerms()).simplify();
  }
}
