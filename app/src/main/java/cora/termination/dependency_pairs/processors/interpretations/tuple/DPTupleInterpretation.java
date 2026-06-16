package cora.termination.dependency_pairs.processors.interpretations.tuple;

import java.util.Map;

import charlie.smt.IVar;
import charlie.smt.SmtFactory;
import charlie.smt.SmtProblem;
import charlie.terms.FunctionSymbol;
import cora.termination.dependency_pairs.DP;

public class DPTupleInterpretation extends RuleTupleInterpretation {
  private final IVar _reductionIndicator;
  private boolean _oriented = false;

  public DPTupleInterpretation(SmtProblem problem, DP dp,
      Map<FunctionSymbol, SymbolTupleInterpretation> symbolInterpretations) {
    super(problem, dp.lhs(), dp.rhs(), symbolInterpretations);
    _reductionIndicator = SmtFactory.createIntegerVariable(
        problem, dp.lhs().queryRoot() + "_red", 0, 1);
  }

  public IVar queryReductionIndicator() {
    return _reductionIndicator;
  }

  @Override
  public void requireWeaklyDecreasing() {
    super.addReductionIndicator(_reductionIndicator);
    super.requireWeaklyDecreasing();
  }

  public void setOriented(boolean oriented) {
    _oriented = oriented;
  }

  public boolean isOriented() {
    return _oriented;
  }
}
