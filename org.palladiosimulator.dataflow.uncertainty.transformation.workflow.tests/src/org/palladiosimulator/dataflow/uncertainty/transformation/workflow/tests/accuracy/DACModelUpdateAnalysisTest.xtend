package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.accuracy

import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.DACAnalysisTests
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.BeforeEach
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate.ModelUpdateTestUtil

class DACModelUpdateAnalysisTest extends DACAnalysisTests {
	
	@BeforeAll
	static def void init() {
		ModelUpdateTestUtil.initTest
	}
	
	@BeforeEach
	override void setup() {
		super.setup();
		builder = new org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate.ModelUpdaterTransformationWorkflowBuilder
	}
	
	protected override initProver() {
		ModelUpdateTestUtil.addUCToBuilder(builder as org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate.ModelUpdaterTransformationWorkflowBuilder)
		(builder as org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate.ModelUpdaterTransformationWorkflowBuilder).addDDC(getRelativeURI("models/evaluation/dac/dac_dd.xmi"))
		super.initProver
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
