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
import java.io.File
import org.palladiosimulator.dataflow.uncertainty.fis.FuzzySystemResultInterpreter

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

		var fis = actModel.fisContainer.get(0).fuzzyInferenceSystems.get(0)
		var fisPath = FisFileGenerator.doGenerate(fis)
		var fisExecution = FuzzySystemExecutionFactory.create()
		
		
		var executionResult = fisExecution.runFIS(List.of(80.0, 1.0), fisPath)
		var maxMembershipName = FuzzySystemResultInterpreter.getMaxMembershipFunction(fis.output.get(0).term, executionResult).name
		assertEquals("mid", maxMembershipName)
		
		executionResult = fisExecution.runFIS(List.of(90.0, 1.0), fisPath)
		maxMembershipName = FuzzySystemResultInterpreter.getMaxMembershipFunction(fis.output.get(0).term, executionResult).name
		assertEquals("high", maxMembershipName)
		
		executionResult = fisExecution.runFIS(List.of(90.0, 9.5), fisPath)
		maxMembershipName = FuzzySystemResultInterpreter.getMaxMembershipFunction(fis.output.get(0).term, executionResult).name
		assertEquals("low", maxMembershipName)
	}
	

}