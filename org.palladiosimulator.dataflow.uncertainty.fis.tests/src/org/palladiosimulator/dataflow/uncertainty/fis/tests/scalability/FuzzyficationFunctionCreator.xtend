package org.palladiosimulator.dataflow.uncertainty.fis.tests.scalability

import java.util.Random
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.FuzzyInferenceSystemFactory
import java.util.ArrayList
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.FuzzyInferenceSystem
import java.util.HashMap
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.FuzzificationFunction
import java.util.List
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.RULE_Operator
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.MembershipFunction
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.AND_Operator
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.ACCU_Method
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.OR_Operator
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.DEFUZZY_Method

class FuzzyficationFunctionCreator {
	
	val fuzzyFactory = FuzzyInferenceSystemFactory.eINSTANCE 
	
	static val RANGE_LOW = 10
	static val RANGE_HIGH = 1000
	
	static val MF_LOW = 2
	static val MF_HIGH = 5
	
	static val RULE_NUMBER = 5
	
	val random = new Random
	
	def generateFISWithInputs(int inputCount) {
		var fis = fuzzyFactory.createFuzzyInferenceSystem
		
		fis.generateFuzzyficationFunctions(inputCount)
		fis.createDefuzzyficationFunction
		fis.generateRules
		
		fis.name = "ScalabilityFIS"
		fis.AND = AND_Operator.MIN
		fis.ACCU = ACCU_Method.MAX
		fis.OR = OR_Operator.MAX
		fis.METHOD = DEFUZZY_Method.COG
		fis
	}
	
	def generateRules(FuzzyInferenceSystem fis) {
		val usedRuleMap = new HashMap<FuzzificationFunction,List<MembershipFunction> >
		usedRuleMap.initializeRuleMap(fis)
		
		// create rules
		for(var i = 0; i < RULE_NUMBER; i++) {
			val rule = fuzzyFactory.createRule
			rule.operator = RULE_Operator.AND
			
			// Add random mfs from each input to rule
			// using map ensures that each mf is used at least once
			fis.input.forEach[fuzzy | 
				var list = usedRuleMap.get(fuzzy)
				var int mfIndex 
				var MembershipFunction mf
				if(list.size == 0) { // all mfs have been used in a rule
					mfIndex = getRandomNumberBetween(0, fuzzy.term.size - 1)
					mf = fuzzy.term.get(mfIndex)
				} else {
					mfIndex = getRandomNumberBetween(0, list.size - 1)
					mf = list.remove(mfIndex)
				}
				rule.inputs.add(mf)
			]
			
			// Add random output mf to rule
			var outputMFIndex = getRandomNumberBetween(0, fis.output.term.size - 1)
			rule.output.add(fis.output.term.get(outputMFIndex))
			fis.rules.add(rule)
		}
	}
	
	def initializeRuleMap(HashMap<FuzzificationFunction,List<MembershipFunction> > map, FuzzyInferenceSystem fis) {
		fis.input.forEach[fuzzy | 
			var list = new ArrayList<MembershipFunction>()
			list.addAll(fuzzy.term)
			map.put(fuzzy, list)
		]
	}
	
	def generateFuzzyficationFunctions(FuzzyInferenceSystem fis, int count) {
		for(var i = 0; i < count; i++) {
			fis.input.add(createFuzzyficationFunction(i))
		}
	}
	
	/**
	 * Creates a defuzzyficationFunction with a range of [0, 100]
	 * three gaussian mfs with sigma 10, spaced 25 away from each other
	 */
	def createDefuzzyficationFunction(FuzzyInferenceSystem fis) {
		var defuzzy = fuzzyFactory.createDefuzzificationFunction
		defuzzy.name = "Trust"
		defuzzy.range.add(0.0)
		defuzzy.range.add(100.0)
		
		for(var i = 1; i <= 3; i++) {
			var mid = i * 25.0 
			var gaussMF = fuzzyFactory.createGaussianMF
			gaussMF.o = 10.0
			gaussMF.m = mid
			gaussMF.name = "trust_" + i
			
			defuzzy.term.add(gaussMF)
		}
		
		fis.output = defuzzy
	}
	
	def createFuzzyficationFunction(int id) {
		var mfNumber = getMFNumber
		var upperRange = getUpperRange
		
		var mfArea = upperRange/mfNumber
		var midArea = mfArea/2
		
		var fuzzyfication = fuzzyFactory.createFuzzificationFunction
		fuzzyfication.name = "Input"+id
		fuzzyfication.range.add(0.0)
		fuzzyfication.range.add(Double.valueOf(upperRange))

		for(var i = 0; i < mfNumber; i++) {
			var currentStart = i * mfArea
			var triMF = fuzzyFactory.createTriangularMF
			triMF.a = currentStart
			triMF.b = currentStart + mfArea
			triMF.m = currentStart + midArea
			triMF.name = fuzzyfication.name + "." + i
			
			fuzzyfication.term.add(triMF)
		}
		
		fuzzyfication
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

	def int getMFNumber() {
		getRandomNumberBetween(MF_LOW, MF_HIGH)
	}
	
	def int getUpperRange() {
		getRandomNumberBetween(RANGE_LOW, RANGE_HIGH)
	}
}