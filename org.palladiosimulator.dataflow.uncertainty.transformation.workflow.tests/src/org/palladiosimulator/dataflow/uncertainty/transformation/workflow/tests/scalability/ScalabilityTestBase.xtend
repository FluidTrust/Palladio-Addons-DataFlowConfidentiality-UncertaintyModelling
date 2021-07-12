package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.scalability

import org.palladiosimulator.dataflow.Uncertainty.UncertaintyFactory
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.UncertaintyTransformationWorkflowBuilder
import org.prolog4j.Prover
import org.prolog4j.IProverFactory
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyContainer
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.DataDictionaryCharacterized
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.util.UncertaintyStandaloneUtil
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyPackage
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.BeforeEach
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.util.StandaloneUtil
import org.prolog4j.swicli.SWIPrologCLIProverFactory
import org.prolog4j.swicli.SWIPrologCLIProverFactory.SWIPrologExecutableProviderStandalone
import org.prolog4j.swicli.enabler.SWIPrologEmbeddedFallbackExecutableProvider
import org.prolog4j.swicli.DefaultSWIPrologExecutableProvider
import java.util.Arrays
import java.io.FileOutputStream
import java.nio.file.Path
import java.nio.file.Files
import java.io.IOException

class ScalabilityTestBase {
	protected static val TEST_RUNS = 1 //10 
	
	protected static val TEST_START = 2
	protected static val ITERATION_FACTOR = 2
	protected static val TEST_ITERATION = 128 //2048
	
	protected static var IProverFactory proverFactory
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