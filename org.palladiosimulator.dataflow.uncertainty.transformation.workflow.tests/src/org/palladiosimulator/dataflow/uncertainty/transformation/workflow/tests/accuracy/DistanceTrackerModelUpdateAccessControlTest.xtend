package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.accuracy

import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.BeforeEach
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.DistanceTrackerAccessControlTest
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate.ModelUpdateTestUtil

class DistanceTrackerModelUpdateAccessControlTest extends DistanceTrackerAccessControlTest {
		
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
		var dfd = super.loadAndInitDFD(ddcPath, dfdPath)
		ModelUpdateTestUtil.addUCToBuilder(builder as org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate.ModelUpdaterTransformationWorkflowBuilder)
		
		dfd
	}
	
	protected override getQuery() {
		ModelUpdateTestUtil.getAccessControlQuery(prover, roleName, roleId, accessRightsName, accessRightsId)	
	}
}
