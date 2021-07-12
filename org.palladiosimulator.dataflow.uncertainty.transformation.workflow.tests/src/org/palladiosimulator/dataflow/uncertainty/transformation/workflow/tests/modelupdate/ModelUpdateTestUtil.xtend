package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate

import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.util.UncertaintyStandaloneUtil
import org.prolog4j.Prover
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.impl.AnalysisIntegrationTestBase
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.DataDictionaryCharacterized
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram

class ModelUpdateTestUtil {
	
	static val ACCESS_CONTROL_QUERY = '''
			inputPin(P, PIN),
			setof(R, nodeCharacteristic(P, ?CTROLES, R, T), ROLES),
			setof_characteristics_with_trust(P, PIN, ?CTRIGHTS, REQ, T, S),
			intersection(REQ, ROLES, []).
		'''
		
	static val ABAC_QUERY = '''
			actor(A),
			inputPin(A,PIN),
			nodeCharacteristic(A, 'EmployeeLocation (_j_v1Y-JAEeqO9NqdRSqKUA)', SUBJ_LOC, LOC_TRUST),
			nodeCharacteristic(A, 'EmployeeRole (_nNduk-JAEeqO9NqdRSqKUA)', SUBJ_ROLE, ROLE_TRUST),
			characteristic(A, PIN, 'CustomerLocation (_h6k4o-JAEeqO9NqdRSqKUA)', OBJ_LOC, ORIG_TRUST, S),
			characteristic(A, PIN, 'CustomerStatus (_lmMOw-JAEeqO9NqdRSqKUA)', OBJ_STAT, STAT_TRUST, S),
			(
				SUBJ_LOC \= OBJ_LOC, SUBJ_ROLE \= 'Manager (_dvk30OJAEeqO9NqdRSqKUA)';
				OBJ_STAT = 'Celebrity (_hCxt8OJAEeqO9NqdRSqKUA)', SUBJ_ROLE \= 'Manager (_dvk30OJAEeqO9NqdRSqKUA)'
			).
		'''
	
	static def getAccessControlQuery(Prover prover, String roleName, String roleId, String accessRightsName, String accessRightsId) {
		var queryString = ACCESS_CONTROL_QUERY
		var query = prover.query(queryString)
		query.bind("CTROLES", '''«roleName» («roleId»)'''.toString)
		query.bind("CTRIGHTS", '''«accessRightsName» («accessRightsId»)'''.toString)	
	}
	
	static def getABACQuery(Prover prover) {
		var queryString = ABAC_QUERY
		var query = prover.query(queryString)
		query
	}
	
	static def initTest() {
		AnalysisIntegrationTestBase.init()
		UncertaintyStandaloneUtil.init();
	}
	
	static def loadAndInitDFD(ModelUpdaterTransformationWorkflowBuilder builder, String ddcPath, String dfdPath) {
		builder.addUCToBuilder
		var resourceSet = new ResourceSetImpl
		var ddUri = UncertaintyStandaloneUtil.getRelativeURI(ddcPath)
		var ddResource = resourceSet.getResource(ddUri, true)
		var dd = ddResource.contents.iterator.next as DataDictionaryCharacterized
		var dfdUri = UncertaintyStandaloneUtil.getRelativeURI(dfdPath)
		var dfdResource = resourceSet.getResource(dfdUri, true)
		var dfd = dfdResource.contents.iterator.next as DataFlowDiagram
		builder.addDFD(dfd, dd);
		dfd
	}
	
	static def addUCToBuilder(ModelUpdaterTransformationWorkflowBuilder builder) {
		builder.addUC(UncertaintyStandaloneUtil.getRelativeURI("models/modelUpdate/modelupdate.uncertainty"))
	}
}