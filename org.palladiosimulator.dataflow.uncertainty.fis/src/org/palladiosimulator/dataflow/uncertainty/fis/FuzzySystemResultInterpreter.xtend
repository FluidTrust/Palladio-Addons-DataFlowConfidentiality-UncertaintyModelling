package org.palladiosimulator.dataflow.uncertainty.fis

import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.MembershipFunction
import java.util.List

class FuzzySystemResultInterpreter {
	
	private new() { }
	
	// transforming the result back to the fuzzy set with the highest membership value
	/**
	 * Transforms the result 
	 */
	static def getMaxMembershipFunction(List<MembershipFunction> terms, double executionResult) {
		var membershipValues = terms.map[t|t.calculateTrustWeight(executionResult)]
		var membership = 0;
		var maxMembershipValue = Double.MIN_VALUE;
		for(var i = 0; i< membershipValues.size; i++) {
			if (membershipValues.get(i) > maxMembershipValue) {
				membership = i
				maxMembershipValue = membershipValues.get(i)
			}
		}
		
		return terms.get(membership)
	}
}