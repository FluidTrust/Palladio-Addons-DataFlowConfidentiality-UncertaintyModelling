package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.scalability

import org.junit.jupiter.api.Test
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.UncertaintyTransformationWorkflowBuilder
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedExternalActor
import org.palladiosimulator.dataflow.Uncertainty.TrustedEnumCharacteristic
import org.palladiosimulator.dataflow.Uncertainty.TrustedEnumCharacteristicType
import org.eclipse.xtext.resource.SaveOptions
import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.NameGenerationStrategie

import static org.junit.jupiter.api.Assertions.*

class PropertyScalabilityTest extends ScalabilityTestBase {
	
	@Test
	def void warmup() {
		println("Warmup")
		for(var i = TEST_START; i <= TEST_ITERATION; i= i*ITERATION_FACTOR) {
				builder = new UncertaintyTransformationWorkflowBuilder();
				testIncreasedProperties(i)
		}
	}
	
	@Test
	def void runScalabilityTest() {
		println("ScalabilityTest")
		for(var testRuns = 0; testRuns < TEST_RUNS; testRuns++) {
			for(var i = TEST_START; i <= TEST_ITERATION; i= i*ITERATION_FACTOR) {
				builder = new UncertaintyTransformationWorkflowBuilder();
				testIncreasedProperties(i)
			}
		}
		
		prologMappingTimeMapper.calculateAndPrintMeanTimes
		
		prologMappingTimeMapper.calculateAndPrintMedianTimes
	}
	
	def testIncreasedProperties(int count) {
		print(count + ": ")
		loadAndInitDFD
		
		var baseType = dataDictionary.characteristicTypes.filter(TrustedEnumCharacteristicType).findFirst["Location" == name]
		
		for(var i = 0; i < count; i++) {
			val newType = uncertaintyFactory.createTrustedEnumCharacteristicType
			newType.type = baseType.type
			newType.trust = baseType.trust
			newType.name = baseType.name + i
			
			dataDictionary.characteristicTypes.add(newType)

			dfd.nodes.filter(CharacterizedExternalActor).forEach[n | 
				var baseChar = n.characteristics.filter(TrustedEnumCharacteristic).findFirst["location" == name]

				var newCharacteristic = uncertaintyFactory.createTrustedEnumCharacteristic
				newCharacteristic.type = newType
				newCharacteristic.trustSource = baseChar.trustSource
				newCharacteristic.name = baseChar.name + "_" + newType.name
				
				n.ownedCharacteristics.add(newCharacteristic)
			]
		}
		
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
		//writeToFile(result.get, "PropertyScalability", count)
		
	}
}