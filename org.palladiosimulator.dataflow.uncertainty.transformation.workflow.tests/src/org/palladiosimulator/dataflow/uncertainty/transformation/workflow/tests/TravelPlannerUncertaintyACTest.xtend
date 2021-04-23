package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests

import java.util.Arrays

import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl

import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.impl.AccessControlAnalysesIflow
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedProcess
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.DataFlowDiagramCharacterizedFactory
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.Behaving
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.DataDictionaryCharacterized

import org.palladiosimulator.dataflow.Uncertainty.UncertaintyContainer
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.UncertaintyTransformationWorkflowBuilder
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyPackage
import org.junit.jupiter.api.BeforeAll
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.util.UncertaintyStandaloneUtil

class TravelPlannerUncertaintyACTest extends AccessControlAnalysesIflow {

	new() {
		super("TrustedRoles", "_-OSe8J3GEeuI4pUKoRa1Cw", "TrustedAccessPermissions", "_xO2TZp3OEeuiD8YzsPy-rw")
	}
	
	@BeforeAll
	static def void init() {
		AccessControlAnalysesIflow.init()
		UncertaintyStandaloneUtil.init();
	}

	@BeforeEach
	override void setup() {
		super.setup();
		builder = new UncertaintyTransformationWorkflowBuilder();
	}

	protected def DataFlowDiagram loadAndInitDFD() {
		UncertaintyPackage.eINSTANCE.getClass
		var resourceSet = new ResourceSetImpl
		var ucUri = getRelativeURI("models/test/TravelPlanner_AccessControl.uncertainty")
		var ucResource = resourceSet.getResource(ucUri, true)
		var uc = ucResource.contents.iterator.next as UncertaintyContainer
		var ddUri = getRelativeURI("models/test/DDC_TravelPlanner_AccessControl.xmi")
		var ddResource = resourceSet.getResource(ddUri, true)
		var dd = ddResource.contents.iterator.next as DataDictionaryCharacterized
		var dfdUri = getRelativeURI("models/test/DFDC_TravelPlanner_AccessControl.xmi")
		var dfdResource = resourceSet.getResource(dfdUri, true)
		var dfd = dfdResource.contents.iterator.next as DataFlowDiagram
		
		(builder as UncertaintyTransformationWorkflowBuilder).addDFD(dfd, dd, uc)
		dfd
	}

	@Test
	def void testNoFlaws() {
		this.loadAndInitDFD
		var solution = findFlaws()
		assertNumberOfSolutions(solution, 0, Arrays.asList("P", "REQ", "ROLES"))
	}

	@Test
	def void testNoDeclassification() {
		var dfd = this.loadAndInitDFD

		// add possible data flow from CCD store to booking process
		var directCCDFlow = DataFlowDiagramCharacterizedFactory.eINSTANCE.createCharacterizedDataFlow
		directCCDFlow.name = "ccd direct"
		directCCDFlow.source = dfd.nodes.filter(CharacterizedProcess).findFirst["CCD.readCCD" == name]
		directCCDFlow.sourcePin = (directCCDFlow.source as Behaving).behavior.outputs.iterator.next
		directCCDFlow.target = dfd.nodes.filter(CharacterizedProcess).findFirst["User.bookFlight" == name]
		directCCDFlow.targetPin = (directCCDFlow.target as Behaving).behavior.inputs.get(1)
		dfd.edges += directCCDFlow

		var solution = findFlaws()
		assertNumberOfSolutions(solution, 3, Arrays.asList("P", "REQ", "ROLES"))
	}

	protected override getQuery() {
		// general no matching characteristic values of node and Pin
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
		// irgendwie ist die Herangehensweise umgekehrt 
		// hole alle sets von werten bei denen die Trusts gleich sind und schaue dann ob es für all diese set denn eine kombination gibt, bei der es keine Intersection gibt
		var queryString2 = '''
			inputPin(P, PIN),
			setof(R, nodeCharacteristic(P, ?CTROLES, R, T), ROLES),
			setof_characteristics_with_trust(P, PIN, ?CTRIGHTS, REQ, T, S),
			intersection(REQ, ROLES, []).
		'''

		

		// get all matching characteristic values
		// check for each match, for not matching corresponding trusts of node and data
		var queryString3 = '''
			inputPin(P, PIN),
			setof(R, nodeCharacteristic(P, ?CTROLES, R, T), ROLES),
			setof_characteristics(P, PIN, ?CTRIGHTS, REQ, ?, S),
			intersection(REQ, ROLES, INTER),
			maplist(nomatch(P, PIN, ?CTROLES2, ?CTRIGHTS2, S), INTER).
		'''
		
		var query = prover.query(queryString2)
		query.bind("CTROLES", '''«roleName» («roleId»)'''.toString)
		query.bind("CTRIGHTS", '''«accessRightsName» («accessRightsId»)'''.toString)
		//query.bind("CTROLES2", '''«roleName» («roleId»)'''.toString)
		//query.bind("CTRIGHTS2", '''«accessRightsName» («accessRightsId»)'''.toString)
		
		return query
	}
	
	protected static def getRelativeURI(String path) {
		return UncertaintyStandaloneUtil.getRelativeURI(path)
	}
}
