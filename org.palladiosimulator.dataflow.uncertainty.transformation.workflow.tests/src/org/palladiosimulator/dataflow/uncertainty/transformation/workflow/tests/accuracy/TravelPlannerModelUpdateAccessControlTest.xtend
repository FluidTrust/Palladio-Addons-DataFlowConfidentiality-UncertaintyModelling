package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.accuracy

import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.BeforeEach
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.TravelPlannerAccessControlTest
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate.ModelUpdateTestUtil

class TravelPlannerModelUpdateAccessControlTest extends TravelPlannerAccessControlTest {
	
	@BeforeAll
	static def void init() {
		ModelUpdateTestUtil.initTest
	}
	
	@BeforeEach
	override void setup() {
		super.setup();
		builder = new org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate.ModelUpdaterTransformationWorkflowBuilder
	}
	
	override DataFlowDiagram loadAndInitDFD(String ddcPath, String dfdPath) {
		ModelUpdateTestUtil.loadAndInitDFD(builder as org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate.ModelUpdaterTransformationWorkflowBuilder, ddcPath, dfdPath)

	}
	
	protected override getQuery() { 
		ModelUpdateTestUtil.getAccessControlQuery(prover, roleName, roleId, accessRightsName, accessRightsId)	
	}
}
