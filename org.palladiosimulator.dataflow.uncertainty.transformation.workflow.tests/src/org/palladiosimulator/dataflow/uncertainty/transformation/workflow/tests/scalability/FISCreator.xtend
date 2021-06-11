package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.scalability

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
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.scalability.FISScalabilityTestUtil

class FISCreator {
	
	static val fuzzyFactory = FuzzyInferenceSystemFactory.eINSTANCE 
	static val scalabilityUtil = FISScalabilityTestUtil.instance
	
	//variables for test Case
	static val RANGE_LOW = 10
	static val RANGE_HIGH = 1000
	static val MF_LOW = 2
	static val MF_HIGH = 5
	static val RULE_COUNT = 5
	
	/**
	 * Called by the FISInputScalabilityTest to get a generated FIS
	 */
	static def generateFISWithInputs(int inputCount) {
		var fis = fuzzyFactory.createFuzzyInferenceSystem
		
		fis.generateFuzzyficationFunctions(inputCount)
		fis.createDefuzzyficationFunction
		fis.generateRules(RULE_COUNT)
		
		fis.name = "ScalabilityFIS"
		fis.AND = AND_Operator.MIN
		fis.ACCU = ACCU_Method.MAX
		fis.OR = OR_Operator.MAX
		fis.METHOD = DEFUZZY_Method.COG
		fis
	}
	
	static def generateRules(FuzzyInferenceSystem fis, int ruleCount) {
		val usedRuleMap = new HashMap<FuzzificationFunction,List<MembershipFunction> >
		usedRuleMap.initializeRuleMap(fis)
		
		// create rules
		for(var i = 0; i < ruleCount; i++) {
			val rule = fuzzyFactory.createRule
			rule.operator = RULE_Operator.AND
			
			// Add random mfs from each input to rule
			// using map ensures that each mf is used at least once
			fis.input.forEach[fuzzy | 
				var list = usedRuleMap.get(fuzzy)
				var int mfIndex 
				var MembershipFunction mf
				if(list.size == 0) { // all mfs have been used in a rule
					mfIndex = scalabilityUtil.getRandomNumberBetween(0, fuzzy.term.size - 1)
					mf = fuzzy.term.get(mfIndex)
				} else {
					mfIndex = scalabilityUtil.getRandomNumberBetween(0, list.size - 1)
					mf = list.remove(mfIndex)
				}
				rule.inputs.add(mf)
			]
			
			// Add random output mf to rule
			var outputMFIndex = scalabilityUtil.getRandomNumberBetween(0, fis.output.term.size - 1)
			rule.output.add(fis.output.term.get(outputMFIndex))
			fis.rules.add(rule)
		}
	}
	
	static def initializeRuleMap(HashMap<FuzzificationFunction,List<MembershipFunction> > map, FuzzyInferenceSystem fis) {
		fis.input.forEach[fuzzy | 
			var list = new ArrayList<MembershipFunction>()
			list.addAll(fuzzy.term)
			map.put(fuzzy, list)
		]
	}
	
	static def generateFuzzyficationFunctions(FuzzyInferenceSystem fis, int count) {
		for(var i = 0; i < count; i++) {
			fis.input.add(createFuzzyficationFunction(i))
		}
	}
	
	/**
	 * Creates a defuzzyficationFunction with a range of [0, 100]
	 * three gaussian mfs with sigma 10, spaced 25 away from each other
	 */
	static def createDefuzzyficationFunction(FuzzyInferenceSystem fis) {
		fis.createDefuzzyFunction(3, 100.0, 25.0, 0.0, 10.0)
	}
	
	static def createLabelScalabilityDefuzzy(FuzzyInferenceSystem fis, int mfCount) {
		fis.createDefuzzyFunction(mfCount, 10240.0, 5.0, 2.5, 1.5)
	}
	
	static def createDefuzzyFunction(FuzzyInferenceSystem fis, int mfCount, double upperRange, double mfSpace, double mfSetoff, double sigma) {
		var defuzzy = fuzzyFactory.createDefuzzificationFunction
		defuzzy.name = "Trust"
		defuzzy.range.add(0.0)
		defuzzy.range.add(upperRange)
		
		for(var i = 1; i <= mfCount; i++) {
			var mid = (i * mfSpace) + mfSetoff
			var gaussMF = fuzzyFactory.createGaussianMF
			gaussMF.o = sigma
			gaussMF.m = mid
			gaussMF.name = "trust_" + i
			
			defuzzy.term.add(gaussMF)
		}
		
		fis.output = defuzzy
	}
	
	static def createFuzzyficationFunction(int id) {
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

	static def int getMFNumber() {
		scalabilityUtil.getRandomNumberBetween(MF_LOW, MF_HIGH)
	}
	
	static def int getUpperRange() {
		scalabilityUtil.getRandomNumberBetween(RANGE_LOW, RANGE_HIGH)
	}
}