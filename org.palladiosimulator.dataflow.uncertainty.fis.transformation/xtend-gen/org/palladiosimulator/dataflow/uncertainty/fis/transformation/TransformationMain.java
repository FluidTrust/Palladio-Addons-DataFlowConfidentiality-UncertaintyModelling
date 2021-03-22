package org.palladiosimulator.dataflow.uncertainty.fis.transformation;

import java.util.Map;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.emf.ecore.xmi.impl.XMIResourceFactoryImpl;
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyPackage;
import org.palladiosimulator.dataflow.Uncertainty.impl.UncertaintyContainerImpl;

@SuppressWarnings("all")
public class TransformationMain {
  public static void main(final String[] args) {
    UncertaintyPackage.eINSTANCE.getClass();
    final Resource.Factory.Registry reg = Resource.Factory.Registry.INSTANCE;
    Map<String, Object> _extensionToFactoryMap = reg.getExtensionToFactoryMap();
    XMIResourceFactoryImpl _xMIResourceFactoryImpl = new XMIResourceFactoryImpl();
    _extensionToFactoryMap.put("*", _xMIResourceFactoryImpl);
    final ResourceSetImpl resSet = new ResourceSetImpl();
    final Resource resource = resSet.getResource(URI.createFileURI("/home/nicolas/Dokumente/Uni/Masterarbeit/runtime-EclipseApplication/test/My.uncertainty"), true);
    EcoreUtil.resolveAll(resSet);
    final EObject model = resource.getContents().get(0);
    final UncertaintyContainerImpl actModel = ((UncertaintyContainerImpl) model);
    FisFileGenerator generator = new FisFileGenerator();
    generator.doGenerate(actModel.getFisContainer().get(0));
  }
}
