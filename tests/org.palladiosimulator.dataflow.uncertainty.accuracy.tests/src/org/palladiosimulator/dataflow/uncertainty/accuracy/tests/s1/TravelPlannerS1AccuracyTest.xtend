package org.palladiosimulator.dataflow.uncertainty.accuracy.tests.s1

import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.BeforeEach
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.TravelPlannerAccessControlTest
import org.palladiosimulator.dataflow.uncertainty.accuracy.modelupdate.ModelUpdateTestUtil
import org.palladiosimulator.dataflow.uncertainty.accuracy.modelupdate.ModelUpdaterTransformationWorkflowBuilder

class TravelPlannerS1AccuracyTest extends TravelPlannerAccessControlTest {
	
	@BeforeAll
	static def void init() {
		ModelUpdateTestUtil.initTest
	}
	
	@BeforeEach
	override void setup() {
		super.setup();
		builder = new ModelUpdaterTransformationWorkflowBuilder
	}
	
	override DataFlowDiagram loadAndInitDFD(String ddcPath, String dfdPath) {
		ModelUpdateTestUtil.loadAndInitDFD(builder as ModelUpdaterTransformationWorkflowBuilder, ddcPath, dfdPath)

	}
	
	protected override getQuery() { 
		ModelUpdateTestUtil.getAccessControlQuery(prover, roleName, roleId, accessRightsName, accessRightsId)	
	}
}
