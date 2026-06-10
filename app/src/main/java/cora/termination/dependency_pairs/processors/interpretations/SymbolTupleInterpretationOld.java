package cora.termination.dependency_pairs.processors.interpretations.tuple;

import java.util.ArrayList;
import java.util.List;

import charlie.smt.IVar;
import charlie.smt.IntegerExpression;
import charlie.smt.SmtFactory;
import charlie.smt.SmtProblem;
import charlie.terms.FunctionSymbol;

public class SymbolTupleInterpretationOld {
    
  private final SmtProblem _problem;
  private final FunctionSymbol _symbol;
  private final String _coefficientPrefix;
  private final int _tupleLength;
  
  private final List<IVar> _constantTerms = new ArrayList<>();

  private final List<List<IVar>> _argumentVariables = new ArrayList<>();

  private List<IntegerExpression> _linearTerms = new ArrayList<>();
  private List<List<IVar>> _linearCoefficients = new ArrayList<>();
    
  public SymbolTupleInterpretationOld(
    SmtProblem problem, FunctionSymbol symbol, 
    String coefficientPrefix, int tupleLenght
  ) {
    if (tupleLenght < 1) throw new IllegalArgumentException("Tuple length must be at least 1");
    
    System.out.println("Creating symbol tuple interpretation for symbol " + symbol.queryName() + " with tuple length " + tupleLenght);

    _problem = problem;
    _symbol = symbol;
    _coefficientPrefix = coefficientPrefix;
    _tupleLength = tupleLenght;

    // Argument variables are shared throughout the tuple, so we create them once here.
    // They have the shape: xn_i, where n is the argument index, and i is the tuple index.
    for (int tupleIndex = 1; tupleIndex <= tupleLenght; tupleIndex++) {
      List<IVar> argVariablesForArg = new ArrayList<>();
      for (int argIndex = 1; argIndex <= symbol.queryArity(); argIndex++) {
        IVar argVariable = SmtFactory.createIntegerVariable(
          problem, 
          "x" + String.valueOf(argIndex) + "_" + String.valueOf(tupleIndex), 
          0, 10
        );
        argVariablesForArg.add(argVariable);
      }
      _argumentVariables.add(argVariablesForArg);
    }

    /*
      Here we generate the tuple for linear interpretations.
      For example, for tuple length k, and number of arguments n, we may construct:

      [[ a(x1, x2, ... xn) ]] = (
        a_c1 + sum_{i=1}^k (a_c1_x1_i * x1_i) + ... + sum_{i=1}^k (a_c1_xn_i * xn_i),
        a_c2 + sum_{i=1}^k (a_c2_x1_i * x1_i) + ... + sum_{i=1}^k (a_c2_xn_i * xn_i),
        ... 
        a_ck + sum_{i=1}^k (a_ck_x1_i * x1_i) + ... + sum_{i=1}^k (a_ck_xn_i * xn_i)
      )

      Here the contants should be read as follows:
        - a is the symbol being interpreted
        - a_cj is the constant term for the j-th element of the tuple
        - a_cj_xm_i is the coefficient for
            the j-th element of the tuple, 
            for the m-th argument, 
            and the i-th element of the tuple that belongs to the m-th argument.
        - xn_i is the i-th element of the tuple that belongs to the n-th argument.
    */
    for (int tupleIndex = 1; tupleIndex <= tupleLenght; tupleIndex++) {
      // Create the constant term for this element of the tuple, i.e., a_cj in the above example.
      IVar constant = SmtFactory.createIntegerVariable(
        problem, coefficientPrefix + symbol.queryName() + "_c" + String.valueOf(tupleIndex), 0, 10
      );
      _constantTerms.add(constant);

      for (int argIndex = 0; argIndex < symbol.queryArity(); argIndex++) {
      
        List<IntegerExpression> subterms = new ArrayList<>();
        List<IVar> coefficientsForArg = new ArrayList<>();
        for (int argTupleIndex = 0; argTupleIndex < tupleLenght; argTupleIndex++) {
          // Create the coefficient for this argument and this element of the tuple, i.e., a_cj_xm_i in the above example.
          IVar coefficient = SmtFactory.createIntegerVariable(
            problem, 
            coefficientPrefix + symbol.queryName() + "_c" + String.valueOf(tupleIndex) + "_x" + String.valueOf(argIndex + 1) + "_" + String.valueOf(argTupleIndex + 1), 
            0, 10
          );
          coefficientsForArg.add(coefficient);

          IVar argVariable = _argumentVariables.get(argTupleIndex).get(argIndex);
          subterms.add(SmtFactory.createMultiplication(coefficient, argVariable));
        }

        _linearTerms.add(SmtFactory.createAddition(subterms).simplify());
        _linearCoefficients.add(coefficientsForArg);
      }
    }

  }
}
