package org.palladiosimulator.dataflow.uncertainty.fis.transformation

import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl
import org.palladiosimulator.dataflow.Uncertainty.impl.UncertaintyFactoryImpl
import org.eclipse.emf.ecore.xmi.impl.XMIResourceFactoryImpl
import org.eclipse.emf.ecore.resource.Resource
import org.eclipse.emf.common.util.URI
import org.eclipse.emf.ecore.EPackage
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyContainer
import org.eclipse.emf.ecore.xmi.impl.EcoreResourceFactoryImpl
import org.eclipse.emf.ecore.util.EcoreUtil
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyPackage
import org.palladiosimulator.dataflow.Uncertainty.impl.UncertaintyContainerImpl
import org.palladiosimulator.dataflow.Uncertainty.util.UncertaintyAdapterFactory

class TransformationMain {
	def static void main(String[] args) {

		UncertaintyPackage.eINSTANCE.getClass
		val reg = Resource.Factory.Registry.INSTANCE
//		reg.getExtensionToFactoryMap().put("ecore", new EcoreResourceFactoryImpl());
      	reg.getExtensionToFactoryMap().put("*", new XMIResourceFactoryImpl)
		val resSet = new ResourceSetImpl()
		
        val resource = resSet.getResource(URI.createFileURI("/home/nicolas/Dokumente/Uni/Masterarbeit/runtime-EclipseApplication/test/My.uncertainty"), true)
        
        EcoreUtil.resolveAll(resSet);
        
        val model = resource.contents.get(0);
        val actModel = model as UncertaintyContainerImpl

		var generator = new FisFileGenerator
		generator.doGenerate(actModel.fisContainer.get(0))

	}
}