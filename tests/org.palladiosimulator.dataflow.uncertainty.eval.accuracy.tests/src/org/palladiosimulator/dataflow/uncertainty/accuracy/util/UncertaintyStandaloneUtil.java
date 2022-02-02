package org.palladiosimulator.dataflow.uncertainty.accuracy.util;

import org.eclipse.emf.common.util.URI;
import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.DFD2PrologTransformation;
import org.palladiosimulator.dataflow.uncertainty.transformation.impl.UncertaintyDFD2PrologTransformationImpl;
import org.palladiosimulator.supporting.prolog.PrologStandaloneSetup;

import tools.mdsd.library.standalone.initialization.StandaloneInitializationException;
import tools.mdsd.library.standalone.initialization.StandaloneInitializer;
import tools.mdsd.library.standalone.initialization.StandaloneInitializerBuilder;
import tools.mdsd.library.standalone.initialization.log4j.Log4jInitilizationTask;

public class UncertaintyStandaloneUtil {

	public static void init() throws StandaloneInitializationException {
        StandaloneInitializer initializer = StandaloneInitializerBuilder.builder()
            .registerProjectURI(DFD2PrologTransformation.class,
                    "org.palladiosimulator.dataflow.confidentiality.transformation.prolog")
            .registerProjectURI(UncertaintyDFD2PrologTransformationImpl.class,
                    "org.palladiosimulator.dataflow.uncertainty.transformation")
            .addCustomTask(new Log4jInitilizationTask())
            .addCustomTask(PrologStandaloneSetup::doSetup)
            .build();
        initializer.init();
    }
	
	
    public static URI getRelativeURI(String relativePath) {
        return URI.createPlatformPluginURI("/org.palladiosimulator.dataflow.uncertainty.accuracy.tests/" + relativePath, false);
    }
}
