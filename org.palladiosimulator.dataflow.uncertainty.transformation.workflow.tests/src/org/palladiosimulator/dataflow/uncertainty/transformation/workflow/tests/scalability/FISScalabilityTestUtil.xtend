package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.scalability

import java.util.List
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.FuzzyInferenceSystem
import java.util.ArrayList
import java.util.Random

class FISScalabilityTestUtil {
	
	static var FISScalabilityTestUtil instance
	val Random random 
	
	private new() {
		random = new Random
	}
	
	static def FISScalabilityTestUtil getInstance() {
		if(instance === null) {
			instance = new FISScalabilityTestUtil
		}
		instance
	}
	
	def List<Double> generateInputsForFIS(FuzzyInferenceSystem fis) {
		val inputs = new ArrayList<Double>
		fis.input.forEach[fuzzy | 
			var in = getRandomInputValue(fuzzy.range.get(1))
			inputs.add(in)
		]
		
		inputs
	}
	
	def int getRandomNumberBetween(int low, int high) {
		// + 1 because nextInt creates a number between 0(inclusive) and the value(exclusive)
		random.nextInt(high - low + 1) + low 
	}
	
	def double getRandomInputValue(double upperRange) {
		var tmp = random.nextFloat
		var input = upperRange * tmp
		input
	}
}