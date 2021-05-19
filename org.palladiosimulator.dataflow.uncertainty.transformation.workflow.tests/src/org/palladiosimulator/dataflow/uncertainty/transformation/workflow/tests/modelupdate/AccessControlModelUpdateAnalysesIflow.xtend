package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate

import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.impl.AccessControlAnalysesIflow
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.util.UncertaintyStandaloneUtil
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.impl.AnalysisIntegrationTestBase
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.BeforeEach
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate.ModelUpdaterTransformationWorkflowBuilder
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.DataDictionaryCharacterized

class AccessControlModelUpdateAnalysesIflow extends AccessControlAnalysesIflow {
	
	new(String roleId, String accessRightsId) {
		super(roleId, accessRightsId)
	}
	
	new (String roleName, String roleId, String accessRightsName, String accessRightsId) {
		super(roleName, roleId, accessRightsName, accessRightsId)
	}
	
	@BeforeAll
	static def void init() {
		AnalysisIntegrationTestBase.init()
		UncertaintyStandaloneUtil.init();
	}
	
	@BeforeEach
	override void setup() {
		super.setup();
		
		builder = new ModelUpdaterTransformationWorkflowBuilder();
	}
	
	override DataFlowDiagram loadAndInitDFD(String ddcPath, String dfdPath) {
		var tmpBuilder = this.builder as ModelUpdaterTransformationWorkflowBuilder
		tmpBuilder.addUC(getRelativeURI("models/modelUpdate/modelupdate.uncertainty"))
		var dfd = super.loadAndInitDFD(ddcPath, dfdPath)
		
		dfd
	}
	
	protected override getQuery() {
		var queryString = '''
			inputPin(P, PIN),
			setof(R, nodeCharacteristic(P, ?CTROLES, R, T), ROLES),
			setof_characteristics_with_trust(P, PIN, ?CTRIGHTS, REQ, T, S),
			intersection(REQ, ROLES, []).
		'''
		var query = prover.query(queryString)
		query.bind("CTROLES", '''«roleName» («roleId»)'''.toString)
		query.bind("CTRIGHTS", '''«accessRightsName» («accessRightsId»)'''.toString)
		
	}
	
	protected override getRelativeURI(String path) {
		return UncertaintyStandaloneUtil.getRelativeURI(path)
	}
}