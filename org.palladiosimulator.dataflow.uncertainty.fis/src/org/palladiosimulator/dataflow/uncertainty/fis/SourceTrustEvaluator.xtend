package org.palladiosimulator.dataflow.uncertainty.fis

import org.palladiosimulator.dataflow.Uncertainty.InformationSource
import org.palladiosimulator.dataflow.uncertainty.fis.transformation.FisFileGenerator
import org.palladiosimulator.dataflow.uncertainty.fis.adapter.FuzzySystemExecutionFactory

class SourceTrustEvaluator {
	
	private new() { }
	
	/**
	 * Executes the given InformationSource and returns the interpreted
	 * MemberschipFunction, the result maps to.
	 * 
	 * */
	static def evaluate(InformationSource source) {
			var fisPath = FisFileGenerator.doGenerate(source.trustSystem)
			var fisExecution = FuzzySystemExecutionFactory.create()
			var executionResult = fisExecution.runFIS(source.fisInputs, fisPath)
			FuzzySystemResultInterpreter.getMaxMembershipFunction(source.trustSystem.output.term, executionResult)
	}
}