package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests

import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyPackage
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyContainer
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.DataDictionaryCharacterized
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.UncertaintyTransformationWorkflowBuilder
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.util.UncertaintyStandaloneUtil
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
import java.io.FileOutputStream
import java.nio.file.Path
import java.nio.file.Files
import java.nio.file.FileSystems
import java.nio.file.Paths
import java.io.IOException

class RunningExampleACTest {
	
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
	def void testLoadAndPrologGeneration() {
		this.loadAndInitDFD
		
		builder.addSerializeToString(SaveOptions.newBuilder.format.getOptions.toOptionsMap)
		builder.setNameDerivationMethod(NameGenerationStrategie.DETAILED)
		var workflow = builder.build

		workflow.run
		var result = workflow.getSerializedPrologProgram
		assertFalse(result.isEmpty)
		
		writeToFile(result.get)

		prover.loadTheory(result.get)

		var solution = query.solve
		
		solution.get
	}
	
		protected def getQuery() {
		var queryString = '''
			inputPin(P, PIN),
			setof(R, nodeCharacteristic(P, ?CTROLES, R, T), ROLES),
			setof_characteristics_with_trust(P, PIN, ?CTRIGHTS, REQ, T, S),
			intersection(REQ, ROLES, []).
		'''
		var query = prover.query(queryString)
		query.bind("CTROLES", '''UserLocation (_SHTJl8dwEeuG_ImeU_5DqQ)'''.toString)
		query.bind("CTRIGHTS", '''ReadAccess (_cC9Ph8dyEeuG_ImeU_5DqQ)'''.toString)
		
	}
	
	protected def DataFlowDiagram loadAndInitDFD() {
		UncertaintyPackage.eINSTANCE.getClass
		var resourceSet = new ResourceSetImpl
		var ucUri = getRelativeURI("models/runningExample/runningExample.uncertainty")
		var ucResource = resourceSet.getResource(ucUri, true)
		var uc = ucResource.contents.iterator.next as UncertaintyContainer
		var ddUri = getRelativeURI("models/runningExample/runningExample.datadictionarycharacterized")
		var ddResource = resourceSet.getResource(ddUri, true)
		var dd = ddResource.contents.iterator.next as DataDictionaryCharacterized
		var dfdUri = getRelativeURI("models/runningExample/runningExample.dataflowdiagram")
		var dfdResource = resourceSet.getResource(dfdUri, true)
		var dfd = dfdResource.contents.iterator.next as DataFlowDiagram
		
		builder.addDFD(dfd, dd, uc)
		dfd
	}
	
	protected static def getRelativeURI(String path) {
		return UncertaintyStandaloneUtil.getRelativeURI(path)
	}
	
	private def writeToFile(String prolog) {
		var FileOutputStream fos
		var Path prologPath = Path.of("/home/nicolas/Dokumente/Uni/FluidTrust/Palladio-Addons-DataFlowConfidentiality-UncertaintyModelling/org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests/models/runningExample/runningExample.pl")
		try {
			if(Files.exists(prologPath)) {
				Files.delete(prologPath)
			}
			Files.createFile(prologPath)
			var prologFile = prologPath.toFile
			fos = new FileOutputStream(prologPath.toString);
			fos.write(prolog.bytes)
		} catch(IOException e) {
			e.printStackTrace
		} finally {
			fos.close
		}
	}
}