package org.palladiosimulator.dataflow.uncertainty.eval.accuracy.tests.s1

import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.ABACAnalysisTests
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.BeforeAll
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram
import org.palladiosimulator.dataflow.uncertainty.eval.accuracy.modelupdate.ModelUpdateTestUtil
import org.palladiosimulator.dataflow.uncertainty.eval.accuracy.modelupdate.ModelUpdaterTransformationWorkflowBuilder

class ABACS1AccuracyTest extends ABACAnalysisTests {
	
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
		ModelUpdateTestUtil.getABACQuery(this.prover)
	}
}
