package org.palladiosimulator.dataflow.uncertainty.fis.tests.scalability

import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.BeforeEach
import org.palladiosimulator.dataflow.uncertainty.fis.transformation.FisFileGenerator
import org.palladiosimulator.dataflow.uncertainty.fis.adapter.FuzzySystemExecutionFactory
import org.palladiosimulator.dataflow.uncertainty.fis.FuzzySystemResultInterpreter
import org.junit.jupiter.api.Test;
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.scalability.ScalabilityTestTimeMapper
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.scalability.FISScalabilityTestUtil
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.scalability.FISCreator

class FISInputScalabilityTest {
	
	static val TEST_RUNS = 10
	
	static val TEST_START = 2
	static val ITERATION_FACTOR = 2
	static val TEST_ITERATION = 2048
	
	var ScalabilityTestTimeMapper genTimeMapper
	var ScalabilityTestTimeMapper runTimeMapper
	
	@BeforeAll
	static def void init() {
		//UncertaintyPackage.eINSTANCE.getClass
		//FuzzyInferenceSystemPackage.eINSTANCE.getClass
	}
	
	@BeforeEach
	def void setup() {
		genTimeMapper = new ScalabilityTestTimeMapper("Gen Times",TEST_START, TEST_ITERATION,ITERATION_FACTOR)
		runTimeMapper = new ScalabilityTestTimeMapper("Run Times", TEST_START, TEST_ITERATION,ITERATION_FACTOR)
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
		
		genTimeMapper.calculateAndPrintMeanTimes
		runTimeMapper.calculateAndPrintMeanTimes
		
		genTimeMapper.calculateAndPrintMedianTimes
		runTimeMapper.calculateAndPrintMedianTimes
	}
	
	def generateAndRunFIS() {
		for(var i = TEST_START; i <= TEST_ITERATION; i= i*ITERATION_FACTOR) {
			print(i + " ")
			var fis = FISCreator.generateFISWithInputs(i)
			var fisInputs = FISScalabilityTestUtil.instance.generateInputsForFIS(fis)
			var beforeGenerate = System.currentTimeMillis
			var fisPath = FisFileGenerator.doGenerate(fis)
			var afterGenerate = System.currentTimeMillis
			
			var fisGenerationTime = afterGenerate - beforeGenerate
			genTimeMapper.addTime(i, fisGenerationTime)
			print("Generation time: " + fisGenerationTime + " ")
			
			var fisExecution = FuzzySystemExecutionFactory.create()
			var beforeRun = System.currentTimeMillis
			var executionResult = fisExecution.runFIS(fisInputs, fisPath)
			var maxMembership = FuzzySystemResultInterpreter.getMaxMembershipFunction(fis.output.term, executionResult)
			var afterRun = System.currentTimeMillis
			
			var fisRunTime = afterRun - beforeRun
			runTimeMapper.addTime(i, fisRunTime)
			print("Run time: " + fisRunTime + " ")
			println("Result: " + maxMembership.name)
		}
	}
}