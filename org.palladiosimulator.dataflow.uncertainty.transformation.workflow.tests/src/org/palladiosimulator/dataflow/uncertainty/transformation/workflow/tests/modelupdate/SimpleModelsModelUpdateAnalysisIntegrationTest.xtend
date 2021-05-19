package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate

import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.SimpleModelsAnalysisIntegrationTest
import org.junit.jupiter.api.BeforeAll
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.util.UncertaintyStandaloneUtil
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import java.io.IOException

class SimpleModelsModelUpdateAnalysisIntegrationTest extends SimpleModelsAnalysisIntegrationTest {
	
	@BeforeAll
	static def void init() {
		ModelUpdateTestUtil.initTest
	}
	
	@BeforeEach
	override void setup() {
		super.setup();
		var tmpBuilder = new ModelUpdaterTransformationWorkflowBuilder();
		tmpBuilder.addDDC(UncertaintyStandaloneUtil.getRelativeURI("models/unitTestExamples/dd_simple.xmi"));
		tmpBuilder.addUC(UncertaintyStandaloneUtil.getRelativeURI("models/modelUpdate/modelupdate.uncertainty"));
		
		builder = tmpBuilder;
	}
	
	@Test
	override void testOtherLoop() throws IOException {
		(this.builder as ModelUpdaterTransformationWorkflowBuilder)
		.addDDC(UncertaintyStandaloneUtil.getRelativeURI("models/unitTestExamples/loop_dd.xmi"));
		super.testOtherLoop
	}
	
	@Test
	override void testFlowTree() {
		(this.builder as ModelUpdaterTransformationWorkflowBuilder)
		.addDDC(UncertaintyStandaloneUtil.getRelativeURI("models/unitTestExamples/DDC_FlowStack.xmi"));
		super.testFlowTree
	}
	
	protected override String getCharacteristicQuery(String node, String pin, String chartype) {
		return "characteristic(" + node + ", " + pin + ", " + chartype + ", V, T, S).";
	}
	
}