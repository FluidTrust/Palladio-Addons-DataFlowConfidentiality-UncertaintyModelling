package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.accuracy

import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.MACAnalysisTests
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.BeforeEach
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate.ModelUpdateTestUtil

class MACModelUpdateAnalysisTest extends MACAnalysisTests {
	
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
		(builder as org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate.ModelUpdaterTransformationWorkflowBuilder).addDDC(getRelativeURI("models/evaluation/mac/mac_dd.xmi"))
		super.initProver
	}
	
	protected override String getAnalysisRules(String classificationType, String clearanceType) '''
		readViolation(N, CLASSIFICATION_VALUE, CLEARANCE_VALUE, S) :-
			CLASSIFICATION_TYPE = '«classificationType»',
			CLEARANCE_TYPE = '«clearanceType»',
			nodeCandidate(N, CLEARANCE_VALUE),
			inputPin(N, PIN),
			characteristic(N, PIN, CLASSIFICATION_TYPE, CLASSIFICATION_VALUE, CLASSIFICATION_TRUST, S),
			characteristicTypeValue(CLASSIFICATION_TYPE, CLASSIFICATION_VALUE, CLASSIFICATION_INDEX),
			characteristicTypeValue(CLEARANCE_TYPE, CLEARANCE_VALUE, CLEARANCE_INDEX),
			CLEARANCE_INDEX > CLASSIFICATION_INDEX.
		
		writeViolation(N, CLEARANCE_VALUE, STORE, CLASSIFICATION_VALUE, S) :-
			CLEARANCE_TYPE = '«clearanceType»',
			CLASSIFICATION_TYPE = '«classificationType»',
			nodeCandidate(N, CLEARANCE_VALUE),
			store(STORE),
			inputPin(STORE, PIN),
			flowTree(STORE, PIN, S),
			traversedNode(S, N),
			nodeCharacteristic(STORE, CLASSIFICATION_TYPE, CLASSIFICATION_VALUE, CLASSIFICATION_TRUST),
			characteristicTypeValue(CLASSIFICATION_TYPE, CLASSIFICATION_VALUE, CLASSIFICATION_INDEX),
			characteristicTypeValue(CLEARANCE_TYPE, CLEARANCE_VALUE, CLEARANCE_INDEX),
			CLEARANCE_INDEX < CLASSIFICATION_INDEX.
		
		nodeCandidate(A, CLEARANCE_VALUE) :-
			CLEARANCE_TYPE = '«clearanceType»',
			actor(A),
			nodeCharacteristic(A, CLEARANCE_TYPE, CLEARANCE_VALUE, CLEARANCE_TRUST).
		
		nodeCandidate(N, CLEARANCE_VALUE) :-
			actor(A),
			actorProcess(N, A),
			nodeCandidate(A, CLEARANCE_VALUE).
	'''
}
