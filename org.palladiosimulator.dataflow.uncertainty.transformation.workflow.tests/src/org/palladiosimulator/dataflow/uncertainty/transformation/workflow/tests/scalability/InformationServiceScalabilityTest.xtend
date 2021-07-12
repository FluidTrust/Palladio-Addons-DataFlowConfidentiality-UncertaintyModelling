package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.scalability

import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.UncertaintyTransformationWorkflowBuilder
import org.junit.jupiter.api.Test
import org.eclipse.xtext.resource.SaveOptions
import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.NameGenerationStrategie

import static org.junit.jupiter.api.Assertions.*
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.FuzzyInferenceSystem
import org.palladiosimulator.dataflow.Uncertainty.TrustedEnumCharacteristicType
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedExternalActor

class InformationServiceScalabilityTest extends ScalabilityTestBase {
	
	@Test
	def void runScalabilityTest() {
		println("ScalabilityTest")
		for(var testRuns = 0; testRuns < TEST_RUNS; testRuns++) {
			for(var i = TEST_START; i <= TEST_ITERATION; i= i*ITERATION_FACTOR) {
				builder = new UncertaintyTransformationWorkflowBuilder();
				testInformationService(i)
			}
		}
		
		prologMappingTimeMapper.calculateAndPrintMeanTimes
		
		prologMappingTimeMapper.calculateAndPrintMedianTimes
	}
	
	def void testInformationService(int count) {
		print(count + ": ")
		loadAndInitDFD
				
		var fis = uncertaintyContainer.fisContainer.get(0).fuzzyInferenceSystems.findFirst["highSensitivityGPSSensor" == name]
		fis.createInformationServices(count)
		
		var type = dataDictionary.characteristicTypes.filter(TrustedEnumCharacteristicType).findFirst["Location" == name]
		type.createCharacteristics
		
		dfd.nodes.filter(CharacterizedExternalActor).forEach[n | 
			n.referencedCharacteristics.addAll(dataDictionary.characteristics)
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
	}
	
	def createInformationServices(FuzzyInferenceSystem fis, int count) {
		for(var i = 0; i < count; i++) {
			var infoService = uncertaintyFactory.createInformationSource
			infoService.name = "Service" + i
			infoService.trustSystem = fis
			infoService.fisInputs.addAll(FISScalabilityTestUtil.instance.generateInputsForFIS(fis))
			uncertaintyContainer.sources.add(infoService)
		}
	}
	
	def createCharacteristics(TrustedEnumCharacteristicType type) {
		for(var i = 0; i < uncertaintyContainer.sources.size; i++) {
			var service = uncertaintyContainer.sources.get(i)
			var characteristic = uncertaintyFactory.createTrustedEnumCharacteristic
			characteristic.name = "Char"+i
			characteristic.type = type
			characteristic.trustSource = service
			dataDictionary.characteristics.add(characteristic)
		}
	}
}