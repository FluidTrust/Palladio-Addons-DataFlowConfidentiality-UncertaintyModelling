package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.jobs;

import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.NameGenerationStrategie;
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.blackboards.KeyValueMDSDBlackboard;
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.jobs.TransformDFDToPrologJob;
import org.palladiosimulator.dataflow.uncertainty.transformation.UncertaintyDFD2PrologTransformationBuilder;

import de.uka.ipd.sdq.workflow.mdsd.blackboard.ModelLocation;

public class TransformUncertaintyDFDtoPrologJob <T extends KeyValueMDSDBlackboard> extends TransformDFDToPrologJob<T>{
	
	private static final boolean UNCERTAINTY_PERFORMANCETWEAKS = false;
	
    public TransformUncertaintyDFDtoPrologJob(ModelLocation dfdLocation, ModelLocation prologLocation, String traceKey,
            NameGenerationStrategie nameGenerationStrategy) {
    	super(dfdLocation, prologLocation, traceKey, nameGenerationStrategy, UNCERTAINTY_PERFORMANCETWEAKS);

        setTransformationBuilder(UncertaintyDFD2PrologTransformationBuilder.create()
            .setNameProvider(nameGenerationStrategy));
    }

	@Override
	public String getName() {
		return "Transform DFD with uncertainty to Prolog";
	}

}
