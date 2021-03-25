package org.palladiosimulator.dataflow.uncertainty.tests

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl
import org.eclipse.emf.ecore.xmi.impl.XMIResourceFactoryImpl
import org.eclipse.emf.ecore.resource.Resource
import org.eclipse.emf.common.util.URI
import org.eclipse.emf.ecore.util.EcoreUtil
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyPackage
import org.palladiosimulator.dataflow.Uncertainty.impl.UncertaintyContainerImpl
import org.palladiosimulator.dataflow.uncertainty.fis.transformation.FisFileGenerator
import java.util.List
import org.palladiosimulator.dataflow.uncertainty.fis.adapter.FuzzySystemExecutionFactory
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.MembershipFunction
import org.eclipse.emf.common.util.EList
import java.io.File

class FISTransformationTest {
	
	@BeforeEach
	def void setUp() throws Exception {
	}

	@AfterEach
	def void tearDown() throws Exception {
	}

	@Test
	def void testTransformation() {
		UncertaintyPackage.eINSTANCE.getClass
		val reg = Resource.Factory.Registry.INSTANCE
//		reg.getExtensionToFactoryMap().put("ecore", new EcoreResourceFactoryImpl());
      	reg.getExtensionToFactoryMap().put("*", new XMIResourceFactoryImpl)
		val resSet = new ResourceSetImpl()
		
        val resource = resSet.getResource(URI.createFileURI(new File("./base/GPS_example.uncertainty").absolutePath), true)
        
        EcoreUtil.resolveAll(resSet);
        
        val model = resource.contents.get(0);
        val actModel = model as UncertaintyContainerImpl

		var generator = new FisFileGenerator
		var fis = actModel.fisContainer.get(0).fuzzyInferenceSystems.get(0)
		var fisPath = generator.doGenerate(fis)
		var fisExecution = FuzzySystemExecutionFactory.create
		
		
		var executionResult = fisExecution.runFIS(List.of(80.0, 1.0), fisPath)
		var maxMembershipName = getMaxMembershipFunction(fis.output.get(0).term, executionResult).name
		assertEquals("mid", maxMembershipName)
		
		executionResult = fisExecution.runFIS(List.of(90.0, 1.0), fisPath)
		maxMembershipName = getMaxMembershipFunction(fis.output.get(0).term, executionResult).name
		assertEquals("high", maxMembershipName)
		
		executionResult = fisExecution.runFIS(List.of(90.0, 9.5), fisPath)
		maxMembershipName = getMaxMembershipFunction(fis.output.get(0).term, executionResult).name
		assertEquals("low", maxMembershipName)
	}
	
	// transforming the result back to the fuzzy set with the highest membership value
	def getMaxMembershipFunction(EList<MembershipFunction> terms, double executionResult) {
		var membershipValues = terms.map[t|t.calculateTrustWeight(executionResult)]
		var membership = 0;
		var maxMembershipValue = Double.MIN_VALUE;
		for(var i = 0; i< membershipValues.size; i++) {
			if (membershipValues.get(i) > maxMembershipValue) {
				membership = i
				maxMembershipValue = membershipValues.get(i)
			}
		}
		
		return terms.get(membership)
	}
}