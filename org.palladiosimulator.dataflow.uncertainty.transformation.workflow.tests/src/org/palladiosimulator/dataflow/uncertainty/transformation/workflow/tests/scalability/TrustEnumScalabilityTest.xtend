package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.scalability

import org.junit.jupiter.api.Test
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.UncertaintyTransformationWorkflowBuilder
import org.palladiosimulator.dataflow.Uncertainty.TrustedEnumCharacteristicType
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.DataDictionaryCharacterizedFactory
import org.eclipse.xtext.resource.SaveOptions
import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.NameGenerationStrategie
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedExternalActor
import org.palladiosimulator.dataflow.Uncertainty.TrustedEnumCharacteristic
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedNode

import static org.junit.jupiter.api.Assertions.*

class TrustEnumScalabilityTest extends ScalabilityTestBase {
	
	@Test
	def void warmup() {
		println("Warmup")
		for(var i = TEST_START; i <= TEST_ITERATION; i= i*ITERATION_FACTOR) {
			builder = new UncertaintyTransformationWorkflowBuilder();
			testTrustedEnum(i)
		}
	}
	
	@Test
	def void runScalabilityTest() {
		println("ScalabilityTest")
		for(var testRuns = 0; testRuns < TEST_RUNS; testRuns++) {
			for(var i = TEST_START; i <= TEST_ITERATION; i= i*ITERATION_FACTOR) {
				builder = new UncertaintyTransformationWorkflowBuilder();
				testTrustedEnum(i)
			}
		}
		
		prologMappingTimeMapper.calculateAndPrintMeanTimes
		
		prologMappingTimeMapper.calculateAndPrintMedianTimes
	}
	
	def testTrustedEnum(int count) {
		print(count + ": ")
		loadAndInitDFD
		
		// modify FIS to have X trust outputs
		val fis = uncertaintyContainer.fisContainer.get(0).fuzzyInferenceSystems.findFirst["highSensitivityGPSSensor" == name]
		FISCreator.createLabelScalabilityDefuzzy(fis, count)
		fis.rules.clear
		FISCreator.generateRules(fis, 27) // 3 inputs with 3 mfs each -> 27 rules cover all combinations
		
		// get a characteristic type from the dfd references and not from the dd
		// as we would have to explicitly set the ones modified from the dd in the dfd...
		var scientist = dfd.nodes.filter(CharacterizedExternalActor).findFirst["Scientist" == name]
		var type = scientist.characteristics.filter(TrustedEnumCharacteristic).findFirst["location" == name].type as TrustedEnumCharacteristicType
		type.modifyEnumeration(count)
		
		
		// update all information services with the new fis and generate random inputs
		uncertaintyContainer.sources.forEach[s | 
			s.fisInputs.clear
			s.fisInputs.addAll(FISScalabilityTestUtil.instance.generateInputsForFIS(fis))
			s.trustSystem = fis
		]
		
		// update information services of characteristics
		dfd.nodes.filter(CharacterizedNode).forEach[a | 
			a.characteristics.filter(TrustedEnumCharacteristic).forEach[c | 
				c.matchAndSwapInformationService
			]
		]
		
		builder.addSerializeToString(SaveOptions.newBuilder.format.getOptions.toOptionsMap)
		builder.setNameDerivationMethod(NameGenerationStrategie.DETAILED)
		var workflow = builder.build

		var beforeRun = System.currentTimeMillis
		workflow.run
		var afterRun = System.currentTimeMillis	
		var mappingTime = afterRun - beforeRun
		println(mappingTime)
		prologMappingTimeMapper.addTime(count, mappingTime)
		var result = workflow.getSerializedPrologProgram
		assertFalse(result.isEmpty)
		//writeToFile(result.get, "TrustEnumScalability", count)
	}
	
	def matchAndSwapInformationService(TrustedEnumCharacteristic c) {
		uncertaintyContainer.sources.forEach[s | 
			if(s.name == c.trustSource.name) {
				c.trustSource = s
			}
		]
	}
	
	def modifyEnumeration(TrustedEnumCharacteristicType type, int count) {
		type.trust.literals.clear
		for(var i = 1; i <= count; i++) {
			var literal = DataDictionaryCharacterizedFactory.eINSTANCE.createLiteral
			literal.name = "trust_" + i // name has to be identical to the created defuzzy mfs
			type.trust.literals.add(literal)
		}
	}
}