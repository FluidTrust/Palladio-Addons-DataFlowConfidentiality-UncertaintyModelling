package org.palladiosimulator.dataflow.uncertainty.eval.accuracy.tests

import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyPackage
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyContainer
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.DataDictionaryCharacterized
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.UncertaintyTransformationWorkflowBuilder
import org.palladiosimulator.dataflow.uncertainty.eval.accuracy.util.UncertaintyStandaloneUtil
import org.prolog4j.IProverFactory
import org.prolog4j.Prover
import org.prolog4j.swicli.SWIPrologCLIProverFactory.SWIPrologExecutableProviderStandalone
import org.prolog4j.swicli.enabler.SWIPrologEmbeddedFallbackExecutableProvider
import org.prolog4j.swicli.DefaultSWIPrologExecutableProvider
import org.prolog4j.swicli.SWIPrologCLIProverFactory
import java.util.Arrays
import org.junit.jupiter.api.BeforeAll
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.util.StandaloneUtil
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import org.eclipse.xtext.resource.SaveOptions
import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.NameGenerationStrategie

import static org.junit.jupiter.api.Assertions.*
import static org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.impl.AnalysisIntegrationTestBase.*

class RunningExampleAnalysisTest {
	
	static var IProverFactory proverFactory;
	protected var UncertaintyTransformationWorkflowBuilder builder;
	protected var Prover prover;
	
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
	}
	
	@Test
	def void scenario1AnalysisTest() {
		testRunningExampleScenario(1,2)	
	}
	
	@Test
	def void scenario2AnalysisTest() {
		testRunningExampleScenario(2,4)
	}
	
	def void testRunningExampleScenario(int index, int expectedSolutions) {
		this.loadAndInitDFD(index)
		
		builder.addSerializeToString(SaveOptions.newBuilder.format.getOptions.toOptionsMap)
		builder.setNameDerivationMethod(NameGenerationStrategie.DETAILED)
		var workflow = builder.build

		workflow.run
		var result = workflow.getSerializedPrologProgram
		assertFalse(result.isEmpty)
		
		prover.loadTheory(result.get)

		var solution = query.solve
		
		assertNumberOfSolutions(solution, expectedSolutions, Arrays.asList("A", "ST", "PIN", "SUBJ_LOC", "SUBJ_TRUST", "S"))
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
	
	protected def DataFlowDiagram loadAndInitDFD(int i) {
		UncertaintyPackage.eINSTANCE.getClass
		var resourceSet = new ResourceSetImpl
		var ucUri = getRelativeURI("models/runningExample/runningExample" + i + ".uncertainty")
		var ucResource = resourceSet.getResource(ucUri, true)
		var uc = ucResource.contents.iterator.next as UncertaintyContainer
		var ddUri = getRelativeURI("models/runningExample/runningExample.datadictionarycharacterized")
		var ddResource = resourceSet.getResource(ddUri, true)
		var dd = ddResource.contents.iterator.next as DataDictionaryCharacterized
		var dfdUri = getRelativeURI("models/runningExample/runningExample" + i + ".dataflowdiagram")
		var dfdResource = resourceSet.getResource(dfdUri, true)
		var dfd = dfdResource.contents.iterator.next as DataFlowDiagram
		
		builder.addDFD(dfd, dd, uc)
		dfd
	}
	
	protected static def getRelativeURI(String path) {
		return UncertaintyStandaloneUtil.getRelativeURI(path)
	}
}