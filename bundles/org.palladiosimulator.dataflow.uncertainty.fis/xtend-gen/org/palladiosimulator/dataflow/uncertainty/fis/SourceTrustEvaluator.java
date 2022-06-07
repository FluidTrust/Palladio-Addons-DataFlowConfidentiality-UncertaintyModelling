package org.palladiosimulator.dataflow.uncertainty.fis;

import java.nio.file.Path;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.MembershipFunction;
import org.palladiosimulator.dataflow.Uncertainty.InformationSource;
import org.palladiosimulator.dataflow.uncertainty.fis.FuzzySystemResultInterpreter;
import org.palladiosimulator.dataflow.uncertainty.fis.adapter.FuzzySystemExecution;
import org.palladiosimulator.dataflow.uncertainty.fis.adapter.FuzzySystemExecutionFactory;
import org.palladiosimulator.dataflow.uncertainty.fis.transformation.FisFileGenerator;

@SuppressWarnings("all")
public class SourceTrustEvaluator {
  private SourceTrustEvaluator() {
  }
  
  /**
   * Executes the given InformationSource and returns the interpreted
   * MemberschipFunction, the result maps to.
   */
  public static MembershipFunction evaluate(final InformationSource source) {
    MembershipFunction _xblockexpression = null;
    {
      Path fisPath = FisFileGenerator.doGenerate(source.getTrustSystem());
      FuzzySystemExecution fisExecution = FuzzySystemExecutionFactory.create();
      double executionResult = fisExecution.runFIS(source.getFisInputs(), fisPath);
      _xblockexpression = FuzzySystemResultInterpreter.getMaxMembershipFunction(source.getTrustSystem().getOutput().getTerm(), executionResult);
    }
    return _xblockexpression;
  }
}
