package org.palladiosimulator.dataflow.uncertainty.accuracy.tests.s1

import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.DACAnalysisTests
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import org.palladiosimulator.dataflow.uncertainty.accuracy.modelupdate.ModelUpdateTestUtil
import org.palladiosimulator.dataflow.uncertainty.accuracy.modelupdate.ModelUpdaterTransformationWorkflowBuilder

class DACS1AccuracyTest extends DACAnalysisTests {
	
	@BeforeAll
	static def void init() {
		ModelUpdateTestUtil.initTest
	}
	
	@BeforeEach
	override void setup() {
		super.setup();
		builder = new ModelUpdaterTransformationWorkflowBuilder
	}
	
	protected def initProver(String dfdPath) {
		ModelUpdateTestUtil.loadAndInitDFD(builder as ModelUpdaterTransformationWorkflowBuilder, "models/evaluation/dac/dac_dd.xmi", dfdPath)

		super.initProver
	}
	
	@Test
	override void testNoFlaw() {
		initProver("models/evaluation/dac/dac_dfd.xmi")
		assertNumberOfSolutions(findReadViolation(), 0, #["A", "STORE", "S"])
		assertNumberOfSolutions(findWriteViolation(), 0, #["A", "STORE", "S"])
	}
	
	@Test
	override void testReadViolation() {
		initProver("models/evaluation/dac/dac_dfd_readViolation.xmi")
		var writeSolution = findWriteViolation()
		var readSolution = findReadViolation()
		
		assertNumberOfSolutions(writeSolution, 0, #["A", "STORE", "S"])
		assertNumberOfSolutions(readSolution, 2, #["A", "STORE", "S"])
	}
	
	@Test
	override void testWriteViolation() {
		initProver("models/evaluation/dac/dac_dfd_writeViolation.xmi")
		var readSolution = findReadViolation()
		var writeSolution = findWriteViolation()
		
		assertNumberOfSolutions(readSolution, 0, #["A", "STORE", "S"])
		assertNumberOfSolutions(writeSolution, 1, #["A", "STORE", "S"])
	}
	
	protected override String getAnalysisRules(String ctIdentity, String ctReadAccess, String ctWriteAccess) '''
		readViolation(A, STORE, S) :-
			CT_IDENTITY = '«ctIdentity»',
			CT_READ = '«ctReadAccess»',
			store(STORE),
			actor(A),
			nodeCharacteristic(A, CT_IDENTITY, C_IDENTITY, C_IDENTITY_TRUST),
			\+ nodeCharacteristic(STORE, CT_READ, C_IDENTITY, C_IDENTITY_TRUST),
			inputPin(A, PIN),
			flowTree(A, PIN, S),
			traversedNode(S, STORE).
			
		writeViolation(A, STORE, S) :-
			CT_IDENTITY = '«ctIdentity»',
			CT_WRITE = '«ctWriteAccess»',
			store(STORE),
			actor(A),
			inputPin(STORE, PIN),
			nodeCharacteristic(A, CT_IDENTITY, C_IDENTITY, C_IDENTITY_TRUST),
			\+ nodeCharacteristic(STORE, CT_WRITE, C_IDENTITY, C_IDENTITY_TRUST),
			flowTree(STORE, PIN, S),
			traversedNode(S, A).
	'''
}
