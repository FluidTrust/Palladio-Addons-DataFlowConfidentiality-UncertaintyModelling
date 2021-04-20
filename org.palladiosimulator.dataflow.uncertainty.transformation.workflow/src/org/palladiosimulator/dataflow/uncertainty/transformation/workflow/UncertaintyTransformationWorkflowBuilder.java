package org.palladiosimulator.dataflow.uncertainty.transformation.workflow;

import java.util.Arrays;

import org.eclipse.emf.common.util.URI;
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyContainer;
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.TransformationWorkflowBuilder;
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.blackboards.KeyValueMDSDBlackboard;
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.jobs.LoadModelJob;
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram;
import org.palladiosimulator.dataflow.dictionary.DataDictionary.DataDictionary;
import org.palladiosimulator.dataflow.uncertainty.transformation.workflow.jobs.TransformUncertaintyDFDtoPrologJob;

import de.uka.ipd.sdq.workflow.blackboard.Blackboard;
import de.uka.ipd.sdq.workflow.jobs.SequentialBlackboardInteractingJob;
import de.uka.ipd.sdq.workflow.mdsd.blackboard.ModelLocation;
import de.uka.ipd.sdq.workflow.mdsd.blackboard.ResourceSetPartition;

public class UncertaintyTransformationWorkflowBuilder extends TransformationWorkflowBuilder {
	
	private static final ModelLocation DEFAULT_UC_LOCATION = new ModelLocation("dfd", URI.createFileURI("tmp/uc.xmi"));
	
	public UncertaintyTransformationWorkflowBuilder addUC(UncertaintyContainer uc) {
		getBlackboard().setContents(DEFAULT_UC_LOCATION, Arrays.asList(uc));
		return this;
	}
	
	public UncertaintyTransformationWorkflowBuilder addDFD(DataFlowDiagram dfd, DataDictionary dd, UncertaintyContainer uc) {
		getBlackboard().removePartition(DEFAULT_DFD_LOCATION.getPartitionID());
		getBlackboard().addPartition(DEFAULT_DFD_LOCATION.getPartitionID(), new ResourceSetPartition());
		getBlackboard().setContents(DEFAULT_UC_LOCATION, Arrays.asList(uc));
		getBlackboard().setContents(DEFAULT_DD_LOCATION, Arrays.asList(dd));
		getBlackboard().setContents(DEFAULT_DFD_LOCATION, Arrays.asList(dfd));
		dfdLocation = DEFAULT_DFD_LOCATION;
		return this;
	}
	
	@Override
	protected SequentialBlackboardInteractingJob<Blackboard<?>> createJobSequence() {
        var jobSequence = new SequentialBlackboardInteractingJob<>("DFD to Prolog Transformation");

        // add model loading job
        var loadDFDJob = new LoadModelJob<>(getDFDLocation());
        jobSequence.add(loadDFDJob);
        
//        var loadUCJob = new LoadModelJob<>(DEFAULT_UC_LOCATION);
//        jobSequence.add(loadUCJob);

        // create transformation job
        getBlackboard().addPartition(getPrologLocation().getPartitionID(), new ResourceSetPartition());
        
        var transformJob = new TransformUncertaintyDFDtoPrologJob<KeyValueMDSDBlackboard>(dfdLocation, getPrologLocation(), DEFAULT_TRACE_KEY, getNameGenerationStrategie());
        jobSequence.add(transformJob);

        // create serialization job
        jobSequence.addAll(getSerializationJobs());
        
        return jobSequence;
	}

}
