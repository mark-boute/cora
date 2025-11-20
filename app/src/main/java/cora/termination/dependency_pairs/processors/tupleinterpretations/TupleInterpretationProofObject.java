package cora.termination.dependency_pairs.processors.tupleinterpretations;

import java.util.List;
import java.util.Set;

import charlie.smt.IntegerExpression;
import cora.io.OutputModule;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;

public class TupleInterpretationProofObject extends ProcessorProofObject {

  private String _reason;
  private Boolean _success = false;
  private List<IntegerExpression> _costFunctions;

  /**
   * A failed proof; SMT-Solver returned NO.
   * @param input
   */
  public TupleInterpretationProofObject(Problem input) {
    super(input);
    System.out.println("TupleInterpretationProofObject $ TODO: represent failed proof without reason");
  }

  /**
   * A MAYBE proof; SMT-Solver did not find a configuration to match the constraints.
   * @param input
   * @param reason The reason returned by the SMT-Solver
   */
  public TupleInterpretationProofObject(Problem input, String reason) {
    super(input);
    _reason = reason;
    System.out.println("TupleInterpretationProofObject $ TODO: represent failed proof with reason: " + reason);
  }

  /**
   * A successful proof; SMT-Solver returned SAT.
   * @param input The input problem
   * @param oriented The indexes of the oriented DPs
   * @param costFunctions The cost functions for each function symbol as interpreted by the tuple interpretation
   */
  public TupleInterpretationProofObject(Problem input, Set<Integer> oriented, List<IntegerExpression> costFunctions) {
    super(input, input.removeDPs(oriented, true));
    _success = costFunctions != null && !costFunctions.isEmpty();
    _costFunctions = costFunctions;
  }

  /**
   * Justifies the proof object by printing to the given output module.
   * 
   * @param module The output module to print to
   */
  @Override
  public void justify(OutputModule module) {
    if (!_success) {
      if (_reason == null) {
        module.println("No suitable tuple interpretation could be found.");
      } else {
        module.println("The SMT-Solver could not find a suitable tuple interpretation:\n" + _reason);
      }
      return;
    }

    module.println("A suitable tuple interpretation was found:");

    // TODO: print the actual interpretation functions per function symbol
    for (IntegerExpression costFunction : _costFunctions) {
      module.println("\tCost function: " + costFunction.toString());
    }
  }

  @Override
  public String queryProcessorName() { return "Tuple Interpretation Processor"; }
}
