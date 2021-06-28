package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.accuracy

import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.ABACAnalysisTests
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.BeforeAll
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate.ModelUpdateTestUtil

class ABACModelUpdateAnalysisTest extends ABACAnalysisTests {
	
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
		ModelUpdateTestUtil.addUCToBuilder(builder as org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate.ModelUpdaterTransformationWorkflowBuilder)
		var dfd = super.loadAndInitDFD(ddcPath, dfdPath)
		
		dfd
	}
	
	protected override getQuery() {
		ModelUpdateTestUtil.getABACQuery(this.prover)
	}
}
