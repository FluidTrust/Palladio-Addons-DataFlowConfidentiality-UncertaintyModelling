package org.palladiosimulator.dataflow.uncertainty.eval.accuracy.s2.tests

import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.tests.impl.AnalysisIntegrationTestBase
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.BeforeEach
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.UncertaintyTransformationWorkflowBuilder
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.DataDictionaryCharacterized
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyContainer
import org.palladiosimulator.dataflow.uncertainty.eval.accuracy.util.UncertaintyStandaloneUtil
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyPackage
import org.prolog4j.Solution
import org.eclipse.xtext.resource.SaveOptions
import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.NameGenerationStrategie

import static org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import org.palladiosimulator.dataflow.uncertainty.eval.accuracy.modelupdate.ModelUpdateTestUtil

class S2ABACAnalysisTest extends AnalysisIntegrationTestBase {
	
	static val DFD_PATH = "models/accuracy/abac/abac_dfd.xmi"
	static val DDC_PATH = "models/accuracy/abac/abac_dd.xmi"
	
	@BeforeAll
	static def void init() {
		ModelUpdateTestUtil.initTest
	}
	
	@BeforeEach
	override void setup() {
		super.setup();
		builder = new UncertaintyTransformationWorkflowBuilder();
	}
	
	@Test
	def void findS0NoFlaws() {
		this.loadAndInitDFD(DDC_PATH, DFD_PATH)
		var solution = findFlaws()
		assertNumberOfSolutions(solution, 0, #["A", "PIN", "LOC", "LOC_TRUST", "ROLE", "ROLE_TRUST", "ORIG", "ORIG_TRUST", "STAT", "STAT_TRUST", "S"])
	}
	
	@Test
	def void findS2FullLocationErrorViolation() {
		this.loadAndInitDFD(DDC_PATH, "models/accuracy/abac/abac_dfd_locationFullError.xmi")
		var solution = findFlaws()
		assertNumberOfSolutions(solution, 24, #["A", "PIN", "LOC", "LOC_TRUST", "ROLE", "ROLE_TRUST", "ORIG", "ORIG_TRUST", "STAT", "STAT_TRUST", "S"])
	}
	
	@Test
	def void findS2RoleViolation() {
		this.loadAndInitDFD(DDC_PATH, "models/accuracy/abac/abac_dfd_roleViolation.xmi")
		var solution = findFlaws()
		assertNumberOfSolutions(solution, 0, #["A", "PIN", "LOC", "LOC_TRUST", "ROLE", "ROLE_TRUST", "ORIG", "ORIG_TRUST", "STAT", "STAT_TRUST", "S"])
	}
	
	@Test
	def void findS2LocationViolation() {
		this.loadAndInitDFD(DDC_PATH, "models/accuracy/abac/abac_dfd_locationViolation.xmi")
		var solution = findFlaws()
		assertNumberOfSolutions(solution, 8, #["A", "PIN", "LOC", "LOC_TRUST", "ROLE", "ROLE_TRUST", "ORIG", "ORIG_TRUST", "STAT", "STAT_TRUST", "S"])
	}
	
	protected def Solution<Object> findFlaws() {
		builder.addSerializeToString(SaveOptions.newBuilder().format().getOptions().toOptionsMap())
		builder.nameDerivationMethod = NameGenerationStrategie.DETAILED
		var workflow = builder.build()

		workflow.run()
		var result = workflow.getSerializedPrologProgram()
		assertFalse(result.isEmpty())

		prover.loadTheory(result.get())
		
		var solution = query.solve()
		solution
	}
	
	protected override DataFlowDiagram loadAndInitDFD(String ddcPath, String dfdPath) {
		UncertaintyPackage.eINSTANCE.getClass // unnecessary?
		var resourceSet = new ResourceSetImpl
		var ucUri = getRelativeURI("models/accuracy/abac/abac.uncertainty")
		var ucResource = resourceSet.getResource(ucUri, true)
		var uc = ucResource.contents.iterator.next as UncertaintyContainer
		var ddUri = getRelativeURI(ddcPath)
		var ddResource = resourceSet.getResource(ddUri, true)
		var dd = ddResource.contents.iterator.next as DataDictionaryCharacterized
		var dfdUri = getRelativeURI(dfdPath)
		var dfdResource = resourceSet.getResource(dfdUri, true)
		var dfd = dfdResource.contents.iterator.next as DataFlowDiagram
		
		(builder as UncertaintyTransformationWorkflowBuilder).addDFD(dfd, dd, uc)
		dfd
	}
	
	protected def getQuery() {
		var queryString = '''
			actor(A),
			inputPin(A,PIN),
			nodeCharacteristic(A, 'EmployeeLocation (_j_v1Y-JAEeqO9NqdRSqKUA)', LOC, LOC_TRUST),
			nodeCharacteristic(A, 'EmployeeRole (_nNduk-JAEeqO9NqdRSqKUA)', ROLE, ROLE_TRUST),
			characteristic(A, PIN, 'CustomerLocation (_h6k4o-JAEeqO9NqdRSqKUA)', ORIG, ORIG_TRUST, S),
			characteristic(A, PIN, 'CustomerStatus (_lmMOw-JAEeqO9NqdRSqKUA)', STAT, STAT_TRUST, S),
			(
				LOC = ORIG, LOC_TRUST \= ORIG_TRUST;
				LOC \= ORIG, (ROLE \= 'Manager (_dvk30OJAEeqO9NqdRSqKUA)'; ROLE_TRUST = 'lowRole (_tLxJMNhKEeufWtDKXe-Ltg)');
				STAT = 'Celebrity (_hCxt8OJAEeqO9NqdRSqKUA)', (ROLE \= 'Manager (_dvk30OJAEeqO9NqdRSqKUA)'; ROLE_TRUST = 'lowRole (_tLxJMNhKEeufWtDKXe-Ltg)')
			).
		'''
		var query = prover.query(queryString)
		query
	}
	
	protected static def getRelativeURI(String path) {
		return UncertaintyStandaloneUtil.getRelativeURI(path)
	}
	
}