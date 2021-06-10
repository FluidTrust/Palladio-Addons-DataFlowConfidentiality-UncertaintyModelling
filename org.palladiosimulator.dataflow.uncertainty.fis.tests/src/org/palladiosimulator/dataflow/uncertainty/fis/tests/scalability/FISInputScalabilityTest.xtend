package org.palladiosimulator.dataflow.uncertainty.fis.tests.scalability

import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.BeforeEach
import org.palladiosimulator.dataflow.uncertainty.fis.transformation.FisFileGenerator
import org.palladiosimulator.dataflow.uncertainty.fis.adapter.FuzzySystemExecutionFactory
import org.palladiosimulator.dataflow.uncertainty.fis.FuzzySystemResultInterpreter
import java.util.List
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.FuzzyInferenceSystem
import java.util.ArrayList
import java.util.HashMap
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyPackage
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.FuzzyInferenceSystemPackage
import org.junit.jupiter.api.Test;
import java.util.Arrays
import java.util.Collections

class FISInputScalabilityTest {
	
	static val TEST_RUNS = 10
	
	static val TEST_START = 2
	static val ITERATION_FACTOR = 2
	static val TEST_ITERATION = 2048
	val fisGenerator = new FuzzyficationFunctionCreator
	
	var HashMap<Integer, List<Long> >generateTimeMap
	var HashMap<Integer, List<Long>> runTimeMap
	
	@BeforeAll
	static def void init() {
		//UncertaintyPackage.eINSTANCE.getClass
		//FuzzyInferenceSystemPackage.eINSTANCE.getClass
	}
	
	@BeforeEach
	def void setup() {
		generateTimeMap = new HashMap<Integer, List<Long> >
		generateTimeMap.initializeTimeMap
		runTimeMap = new HashMap<Integer, List<Long> >
		runTimeMap.initializeTimeMap
	}
	
	@Test
	def void testWarmup() {
		println("Warmup")
		for(var testRuns = 0; testRuns < 2; testRuns++) {
			generateAndRunFIS
		}
	}
	
	@Test
	def void runScalabilityTest() {
		println("ScalabilityTest")
		for(var testRuns = 0; testRuns < TEST_RUNS; testRuns++) {
			generateAndRunFIS
		}
		
		calculateAndPrintMeanTimes
		calculateAndPrintMedianTimes
	}
	
	def generateAndRunFIS() {
		for(var i = TEST_START; i <= TEST_ITERATION; i= i*ITERATION_FACTOR) {
			print(i + " ")
			var fis = fisGenerator.generateFISWithInputs(i)
			var fisInputs = fis.generateInputsForFIS
			var beforeGenerate = System.currentTimeMillis
			var fisPath = FisFileGenerator.doGenerate(fis)
			var afterGenerate = System.currentTimeMillis
			
			var fisGenerationTime = afterGenerate - beforeGenerate
			generateTimeMap.get(i).add(fisGenerationTime)
			print("Generation time: " + fisGenerationTime + " ")
			
			var fisExecution = FuzzySystemExecutionFactory.create()
			var beforeRun = System.currentTimeMillis
			var executionResult = fisExecution.runFIS(fisInputs, fisPath)
			var maxMembership = FuzzySystemResultInterpreter.getMaxMembershipFunction(fis.output.term, executionResult)
			var afterRun = System.currentTimeMillis
			
			var fisRunTime = afterRun - beforeRun
			runTimeMap.get(i).add(fisRunTime)
			print("Run time: " + fisRunTime + " ")
			println("Result: " + maxMembership.name)
		}
	}
	
	def void calculateAndPrintMeanTimes() {
		var avgGenTimes = new ArrayList<Long>
		var avgRunTimes = new ArrayList<Long>
		for(var i = TEST_START; i <= TEST_ITERATION; i= i*ITERATION_FACTOR) {
			var avgGenTime = generateTimeMap.get(i).calculateMean
			var avgRunTime = runTimeMap.get(i).calculateMean
			
			avgGenTimes.add(avgGenTime)
			avgRunTimes.add(avgRunTime)
		}
		
		println("Mean Gen Times: " + avgGenTimes.toString)
		println("Mean Run Times: " + avgRunTimes.toString)
	}
	
	def void calculateAndPrintMedianTimes() {
		var avgGenTimes = new ArrayList<Long>
		var avgRunTimes = new ArrayList<Long>
		for(var i = TEST_START; i <= TEST_ITERATION; i= i*ITERATION_FACTOR) {
			var avgGenTime = generateTimeMap.get(i).calculateMedian
			var avgRunTime = runTimeMap.get(i).calculateMedian
			
			avgGenTimes.add(avgGenTime)
			avgRunTimes.add(avgRunTime)
		}
		
		println("Median Gen Times: " + avgGenTimes.toString)
		println("Median Run Times: " + avgRunTimes.toString)
	}
	
	def calculateMean(List<Long> list) {
		var long sum = 0
		for(long tmp : list) {
			sum += tmp
		}
		(sum/list.size)
	}
	
	def calculateMedian(List<Long> list) {
		Collections.sort(list)
		var long median
		if (list.size % 2 == 0) {
			median = (list.get(list.size/2) + list.get(list.size/2 - 1))/2
		} else {
			median = list.get(list.size/2)
		}
		median
	}
	
	def List<Double> generateInputsForFIS(FuzzyInferenceSystem fis) {
		val inputs = new ArrayList<Double>
		fis.input.forEach[fuzzy | 
			var in = fisGenerator.getRandomInputValue(fuzzy.range.get(1))
			inputs.add(in)
		]
		
		inputs
	}
	
	def void initializeTimeMap(HashMap<Integer, List<Long> > map) {
		for(var i = TEST_START; i <= TEST_ITERATION; i= i*ITERATION_FACTOR) {
			map.put(i, new ArrayList<Long>)
		}
	}
}