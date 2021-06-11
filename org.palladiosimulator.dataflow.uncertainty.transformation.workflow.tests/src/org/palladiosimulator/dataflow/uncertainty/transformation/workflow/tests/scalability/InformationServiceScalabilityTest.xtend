package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.scalability

import org.prolog4j.IProverFactory
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.UncertaintyTransformationWorkflowBuilder
import org.prolog4j.Prover
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyPackage
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.util.UncertaintyStandaloneUtil
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyContainer
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.DataDictionaryCharacterized
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.util.StandaloneUtil
import org.prolog4j.swicli.SWIPrologCLIProverFactory
import org.prolog4j.swicli.SWIPrologCLIProverFactory.SWIPrologExecutableProviderStandalone
import java.util.Arrays
import org.prolog4j.swicli.DefaultSWIPrologExecutableProvider
import org.prolog4j.swicli.enabler.SWIPrologEmbeddedFallbackExecutableProvider
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import org.eclipse.xtext.resource.SaveOptions
import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.NameGenerationStrategie

import static org.junit.jupiter.api.Assertions.*
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyFactory
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.FuzzyInferenceSystem
import org.palladiosimulator.dataflow.Uncertainty.TrustedEnumCharacteristicType
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedExternalActor

class InformationServiceScalabilityTest {
	
	static val TEST_RUNS = 10
	
	static val TEST_START = 2
	static val ITERATION_FACTOR = 2
	static val TEST_ITERATION = 2048
	
	static var IProverFactory proverFactory
	protected var UncertaintyTransformationWorkflowBuilder builder
	protected var Prover prover
	
	protected var UncertaintyFactory uncertaintyFactory
	
	protected var UncertaintyContainer uncertaintyContainer
	protected var DataFlowDiagram dfd
	protected var DataDictionaryCharacterized dataDictionary
	
	protected var ScalabilityTestTimeMapper prologMappingTimeMapper
	
	@BeforeAll
	static def void init() {
		StandaloneUtil.init();
		var factory = new SWIPrologCLIProverFactory(
			Arrays.asList(new SWIPrologExecutableProviderStandalone(new DefaultSWIPrologExecutableProvider(), 2),
				new SWIPrologExecutableProviderStandalone(new SWIPrologEmbeddedFallbackExecutableProvider(), 1)));
		proverFactory = factory;
		UncertaintyStandaloneUtil.init();
	}
	
	@BeforeEach
	def void setup() {
		builder = new UncertaintyTransformationWorkflowBuilder();
		prover = proverFactory.createProver();
		
		uncertaintyFactory = UncertaintyFactory.eINSTANCE
		
		prologMappingTimeMapper = new ScalabilityTestTimeMapper("Prolog Mapping Time: ", TEST_START, TEST_ITERATION,ITERATION_FACTOR)
	}
	
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

//		prover.loadTheory(result.get)
//
//		var solution = query.solve
//		
//		assertTrue(solution.success)
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
	
	protected def loadAndInitDFD() {
		UncertaintyPackage.eINSTANCE.getClass
		var resourceSet = new ResourceSetImpl
		var ucUri = getRelativeURI("models/runningExample/runningExample1.uncertainty")
		var ucResource = resourceSet.getResource(ucUri, true)
		uncertaintyContainer = ucResource.contents.iterator.next as UncertaintyContainer
		var ddUri = getRelativeURI("models/runningExample/runningExample.datadictionarycharacterized")
		var ddResource = resourceSet.getResource(ddUri, true)
		dataDictionary = ddResource.contents.iterator.next as DataDictionaryCharacterized
		var dfdUri = getRelativeURI("models/runningExample/runningExample1.dataflowdiagram")
		var dfdResource = resourceSet.getResource(dfdUri, true)
		dfd = dfdResource.contents.iterator.next as DataFlowDiagram
		
		builder.addDFD(dfd, dataDictionary, uncertaintyContainer)
	}
	
	protected static def getRelativeURI(String path) {
		return UncertaintyStandaloneUtil.getRelativeURI(path)
	}
	
	protected def getQuery() {
		var queryString = '''
		actor(A), 
		store(ST), 
		nodeCharacteristic(A, 'Location (_o7_1k9VeEeqRbpVUMz5XAQ)', SUBJ_LOC, SUBJ_TRUST), 
		\+ nodeCharacteristic(ST, 'Read Access (_rd9cA9VeEeqRbpVUMz5XAQ)', SUBJ_LOC, SUBJ_TRUST), 
		inputPin(A,PIN), 
		flowTree(A,PIN,S), 
		traversedNode(S,ST).
		'''
		
		var query = prover.query(queryString)
		query	
	}
	
}