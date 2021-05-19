package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate

import org.junit.jupiter.api.Test
import java.util.Arrays
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.DataFlowDiagramCharacterizedFactory
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedProcess
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.Behaving

class ContactSMSModelUpdateAccessControlTest extends AccessControlModelUpdateAnalysesIflow {
	
	new() {
		super("_g8Baw0NEEeq3NrD2DjPidQ", "_fCiJk0NEEeq3NrD2DjPidQ")
	}
	
	@Test
	def void testNoFlaws() {
		loadAndInitDFD("models/modelUpdate/contactsms/DDC_ContactSMS_AccessControl.xmi",
			"models/modelUpdate/contactsms/DFDC_ContactSMS_AccessControl.xmi")
		var solution = findFlaws()
		assertNumberOfSolutions(solution, 0, Arrays.asList("P", "REQ", "ROLES", "S"))
	}
	
	@Test
	def void testNoDeclassification() {		
		var dfd = loadAndInitDFD("models/modelUpdate/contactsms/DDC_ContactSMS_AccessControl.xmi",
			"models/modelUpdate/contactsms/DFDC_ContactSMS_AccessControl.xmi")
		
		// add possible data flow of contact to SMS sending process
		var directCCDFlow = DataFlowDiagramCharacterizedFactory.eINSTANCE.createCharacterizedDataFlow
		directCCDFlow.name = "contact direct"
		directCCDFlow.source = dfd.nodes.filter(CharacterizedProcess).findFirst[name.toLowerCase.contains("selectcontact")]
		directCCDFlow.sourcePin = (directCCDFlow.source as Behaving).behavior.outputs.iterator.next
		directCCDFlow.target = dfd.nodes.filter(CharacterizedProcess).findFirst[name.toLowerCase.contains("sendsms")]
		directCCDFlow.targetPin = (directCCDFlow.target as Behaving).behavior.inputs.get(1)
		dfd.edges += directCCDFlow
		
		var solution = findFlaws()
		assertNumberOfSolutions(solution, 4, Arrays.asList("P", "REQ", "ROLES", "S"))
	}
	
}