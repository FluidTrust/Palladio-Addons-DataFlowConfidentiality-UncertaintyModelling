package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests

import org.junit.jupiter.api.BeforeEach

import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.UncertaintyTransformationWorkflowBuilder
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.DataDictionaryCharacterized
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyContainer
import org.eclipse.xtext.resource.SaveOptions
import org.prolog4j.Solution

import static org.junit.jupiter.api.Assertions.*
import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.NameGenerationStrategie
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.impl.AccessControlAnalysesIflow

class TravelPlannerUncertaintyACTest extends AccessControlAnalysesIflow {

	new(String roleId, String accessRightsId) {
		super(roleId, accessRightsId)
	}
	
	@BeforeEach
	override void setup() {
		super.setup();
		builder = new UncertaintyTransformationWorkflowBuilder();
	} 
	
	protected def DataFlowDiagram loadAndInitDFD(String ddcPath, String dfdPath, String ucPath) {
		var resourceSet = new ResourceSetImpl
		var ddUri = getRelativeURI(ddcPath)
		var ddResource = resourceSet.getResource(ddUri, true)
		var dd = ddResource.contents.iterator.next as DataDictionaryCharacterized
		var dfdUri = getRelativeURI(dfdPath)
		var dfdResource = resourceSet.getResource(dfdUri, true)
		var dfd = dfdResource.contents.iterator.next as DataFlowDiagram
		var ucUri = getRelativeURI(ucPath)
		var ucResource = resourceSet.getResource(ucUri, true)
		var uc = ucResource.contents.iterator.next as UncertaintyContainer
		
		builder.addDFD(dfd, dd)
		(builder as UncertaintyTransformationWorkflowBuilder).addUC(uc)
		dfd
	}
	
	protected override getQuery() {
		//general no matching characteristic values of node and Pin
		var queryString = '''
			inputPin(P, PIN),
			setof(R, nodeCharacteristic(P, ?CTROLES, R, T), ROLES),
			setof_characteristics(P, PIN, ?CTRIGHTS, REQ, S),
			intersection(REQ, ROLES, []).
		'''
		
		// extended variant of using setof_characteristic
		// only get the set of characteristics with trust T
		// only node and data chars where at least the trust is equal are saved in the corresponding sets
		// intersection then only checks if the values are the same
		//irgendwie ist die Herangehensweise umgekehrt 
		// hole alle sets von werten bei denen die Trusts gleich sind und schaue dann ob es für all diese set denn eine kombination gibt, bei der es keine Intersection gibt
		var queryString2 = '''
			inputPin(P, PIN),
			setof(R, nodeCharacteristic(P, ?CTROLES, R, T), ROLES),
			setof_characteristics_with_trust(P, PIN, ?CTRIGHTS, REQ, T, S),
			intersection(REQ, ROLES, []).
		'''
		
		var query = prover.query(queryString)
		query.bind("CTROLES", '''«roleName» («roleId»)'''.toString)
		query.bind("CTRIGHTS", '''«accessRightsName» («accessRightsId»)'''.toString)
	
		// get all matching characteristic values
		// check for each match, for not matching corresponding trusts of node and data
		// nomatch muss dann noch in die Präambel
		var queryString3 = '''
			inputPin(P, PIN),
			setof(R, nodeCharacteristic(P, ?CTROLES, R, T), ROLES),
			setof_characteristics(P, PIN, ?CTRIGHTS, REQ, S),
			intersection(REQ, ROLES, INTER),
			maplist(nomatch(P, PIN, ?CTROLES, ?CTRIGHTS, S), INTER),
			nomatch(P, PIN, NODECHARTYPE, DATACHARTYPE, V) :- setof(T1, nodeCharacteristic(P, NODECHARTYPE, V, T1), NODETRUST),
			setof_characteristic_trusts(P, PIN, DATACHARTYPE, V, DATATRUST, S),
			intersection(NODETRUST, DATATRUST, []).
		'''
		
		return query
	}
}