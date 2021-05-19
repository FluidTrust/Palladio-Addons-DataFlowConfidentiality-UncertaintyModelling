package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate

import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.util.UncertaintyStandaloneUtil
import org.prolog4j.Prover
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.impl.AnalysisIntegrationTestBase

class ModelUpdateTestUtil {
	
	static val ACCESS_CONTROL_QUERY = '''
			inputPin(P, PIN),
			setof(R, nodeCharacteristic(P, ?CTROLES, R, T), ROLES),
			setof_characteristics_with_trust(P, PIN, ?CTRIGHTS, REQ, T, S),
			intersection(REQ, ROLES, []).
		'''
	
	static def getQuery(Prover prover, String roleName, String roleId, String accessRightsName, String accessRightsId) {
		var queryString = ACCESS_CONTROL_QUERY
		var query = prover.query(queryString)
		query.bind("CTROLES", '''«roleName» («roleId»)'''.toString)
		query.bind("CTRIGHTS", '''«accessRightsName» («accessRightsId»)'''.toString)	
	}
	
	static def initTest() {
		AnalysisIntegrationTestBase.init()
		UncertaintyStandaloneUtil.init();
	}
	
	static def addUCToBuilder(ModelUpdaterTransformationWorkflowBuilder builder) {
		builder.addUC(UncertaintyStandaloneUtil.getRelativeURI("models/modelUpdate/modelupdate.uncertainty"))
	}
}