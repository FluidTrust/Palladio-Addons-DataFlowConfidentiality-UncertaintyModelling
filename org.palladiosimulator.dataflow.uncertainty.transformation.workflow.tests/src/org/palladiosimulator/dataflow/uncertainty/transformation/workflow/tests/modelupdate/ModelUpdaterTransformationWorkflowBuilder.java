package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.modelupdate;

import org.eclipse.emf.common.util.URI;
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.TransformationWorkflowBuilder;
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.blackboards.KeyValueMDSDBlackboard;
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.jobs.LoadModelJob;
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.UncertaintyTransformationWorkflowBuilder;
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.jobs.DFDModelUpdaterJob;

import de.uka.ipd.sdq.workflow.blackboard.Blackboard;
import de.uka.ipd.sdq.workflow.jobs.SequentialBlackboardInteractingJob;
import de.uka.ipd.sdq.workflow.mdsd.blackboard.ModelLocation;
import de.uka.ipd.sdq.workflow.mdsd.blackboard.ResourceSetPartition;

public class ModelUpdaterTransformationWorkflowBuilder extends UncertaintyTransformationWorkflowBuilder {
	
	private static int JOB_SEQUENCE_ADDITION_INDEX = 1;
	
	// Only needed for testing
	public void addDDC(URI ddcURI) {
		ddcLocation = new ModelLocation(DEFAULT_DFD_LOCATION.getPartitionID(), ddcURI);
	}
	
	// Only needed for testing
	public void addUC(URI ucURI) {
		ucLocation = new ModelLocation(DEFAULT_DFD_LOCATION.getPartitionID(), ucURI);
	}

	@Override
	protected SequentialBlackboardInteractingJob<Blackboard<?>> createJobSequence() {
        var jobSequence = super.createJobSequence();
        
        // As the ddc and uc are going to be modified, they need to be explicitly loaded to the blackboard.
        // As different tests require different ways of loading the models, 
        // checks for varying model locations need to be made when creating the load jobs.
        var loadDDCJob = ddcLocation == null ? new LoadModelJob<>(DEFAULT_DD_LOCATION) : new LoadModelJob<>(ddcLocation);
        jobSequence.add(JOB_SEQUENCE_ADDITION_INDEX, loadDDCJob);
        
        var loadUCJob = ucLocation == null ? new LoadModelJob<>(DEFAULT_UC_LOCATION) : new LoadModelJob<>(ucLocation);
        jobSequence.add(JOB_SEQUENCE_ADDITION_INDEX+1, loadUCJob);
        
        jobSequence.add(JOB_SEQUENCE_ADDITION_INDEX+2, new DFDModelUpdaterJob<KeyValueMDSDBlackboard>(dfdLocation, ddcLocation, ucLocation));
        
        return jobSequence;
	}
}
