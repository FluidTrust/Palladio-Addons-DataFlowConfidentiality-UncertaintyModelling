package org.palladiosimulator.dataflow.uncertainty.tests;

import java.io.File;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.emf.ecore.xmi.impl.XMIResourceFactoryImpl;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.FuzzyInferenceSystem;
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyPackage;
import org.palladiosimulator.dataflow.Uncertainty.impl.UncertaintyContainerImpl;
import org.palladiosimulator.dataflow.uncertainty.fis.FuzzySystemResultInterpreter;
import org.palladiosimulator.dataflow.uncertainty.fis.adapter.FuzzySystemExecution;
import org.palladiosimulator.dataflow.uncertainty.fis.adapter.FuzzySystemExecutionFactory;
import org.palladiosimulator.dataflow.uncertainty.fis.transformation.FisFileGenerator;

@SuppressWarnings("all")
public class FISTransformationTest {
  @BeforeEach
  public void setUp() throws Exception {
  }
  
  @AfterEach
  public void tearDown() throws Exception {
  }
  
  @Test
  public void testTransformation() {
    UncertaintyPackage.eINSTANCE.getClass();
    final Resource.Factory.Registry reg = Resource.Factory.Registry.INSTANCE;
    Map<String, Object> _extensionToFactoryMap = reg.getExtensionToFactoryMap();
    XMIResourceFactoryImpl _xMIResourceFactoryImpl = new XMIResourceFactoryImpl();
    _extensionToFactoryMap.put("*", _xMIResourceFactoryImpl);
    final ResourceSetImpl resSet = new ResourceSetImpl();
    final Resource resource = resSet.getResource(URI.createFileURI(new File("./base/GPS_example.uncertainty").getAbsolutePath()), true);
    EcoreUtil.resolveAll(resSet);
    final EObject model = resource.getContents().get(0);
    final UncertaintyContainerImpl actModel = ((UncertaintyContainerImpl) model);
    FuzzyInferenceSystem fis = actModel.getFisContainer().get(0).getFuzzyInferenceSystems().get(0);
    Path fisPath = FisFileGenerator.doGenerate(fis);
    FuzzySystemExecution fisExecution = FuzzySystemExecutionFactory.create();
    double executionResult = fisExecution.runFIS(List.<Double>of(Double.valueOf(80.0), Double.valueOf(1.0)), fisPath);
    String maxMembershipName = FuzzySystemResultInterpreter.getMaxMembershipFunction(fis.getOutput().get(0).getTerm(), executionResult).getName();
    Assertions.assertEquals("mid", maxMembershipName);
    executionResult = fisExecution.runFIS(List.<Double>of(Double.valueOf(90.0), Double.valueOf(1.0)), fisPath);
    maxMembershipName = FuzzySystemResultInterpreter.getMaxMembershipFunction(fis.getOutput().get(0).getTerm(), executionResult).getName();
    Assertions.assertEquals("high", maxMembershipName);
    executionResult = fisExecution.runFIS(List.<Double>of(Double.valueOf(90.0), Double.valueOf(9.5)), fisPath);
    maxMembershipName = FuzzySystemResultInterpreter.getMaxMembershipFunction(fis.getOutput().get(0).getTerm(), executionResult).getName();
    Assertions.assertEquals("low", maxMembershipName);
  }
}
