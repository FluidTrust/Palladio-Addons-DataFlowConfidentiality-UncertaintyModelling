package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.jobs;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.emf.cdo.CDOLock;
import org.eclipse.emf.cdo.CDOObjectHistory;
import org.eclipse.emf.cdo.CDOState;
import org.eclipse.emf.cdo.common.id.CDOID;
import org.eclipse.emf.cdo.common.lock.CDOLockState;
import org.eclipse.emf.cdo.common.revision.CDORevision;
import org.eclipse.emf.cdo.common.security.CDOPermission;
import org.eclipse.emf.cdo.eresource.CDOResource;
import org.eclipse.emf.cdo.view.CDOView;
import org.eclipse.emf.common.notify.Adapter;
import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EOperation;
import org.eclipse.emf.ecore.EReference;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.ecore.resource.Resource;
import org.palladiosimulator.dataflow.Uncertainty.InformationSource;
import org.palladiosimulator.dataflow.Uncertainty.TrustedContainerCharacteristicReference;
import org.palladiosimulator.dataflow.Uncertainty.TrustedDataCharacteristicReference;
import org.palladiosimulator.dataflow.Uncertainty.TrustedEnumCharacteristicType;
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyContainer;
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyFactory;
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.blackboards.KeyValueMDSDBlackboard;
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram;
import org.palladiosimulator.dataflow.dictionary.DataDictionary.util.DataDictionaryAdapterFactory;
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.Assignment;
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.DataDictionaryCharacterized;
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.DataDictionaryCharacterizedFactory;
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.EnumCharacteristicType;
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.Enumeration;
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.Literal;
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.expressions.BinaryLogicTerm;
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.expressions.ContainerCharacteristicReference;
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.expressions.DataCharacteristicReference;
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.expressions.Term;
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.expressions.UnaryLogicTerm;

import de.uka.ipd.sdq.workflow.jobs.AbstractBlackboardInteractingJob;
import de.uka.ipd.sdq.workflow.jobs.CleanupFailedException;
import de.uka.ipd.sdq.workflow.jobs.JobFailedException;
import de.uka.ipd.sdq.workflow.jobs.UserCanceledException;
import de.uka.ipd.sdq.workflow.mdsd.blackboard.ModelLocation;

public class DFDModelUpdaterJob<T extends KeyValueMDSDBlackboard> extends AbstractBlackboardInteractingJob<T> {

	private ModelLocation dfdLocation;
	private ModelLocation ddcLocation;
	private ModelLocation ucLocation;
	
	private ArrayList<TrustedEnumCharacteristicType> trustedCharTypes = new ArrayList<>();
	
	private Enumeration defaultTrustEnum = DataDictionaryCharacterizedFactory.eINSTANCE.createEnumeration();
	private Literal defaultTrustLiteral = DataDictionaryCharacterizedFactory.eINSTANCE.createLiteral();

	public DFDModelUpdaterJob(ModelLocation dfdLocation, ModelLocation ddcLocation, ModelLocation ucLocation) {
		this.dfdLocation = dfdLocation;
		this.ddcLocation = ddcLocation;
	}

	@Override
	public void execute(IProgressMonitor monitor) throws JobFailedException, UserCanceledException {

		var dfd = getSingleModelFromBlackboard(dfdLocation, DataFlowDiagram.class);
		var ddc = getSingleModelFromBlackboard(ddcLocation, DataDictionaryCharacterized.class);
		var uc = getSingleModelFromBlackboard(ucLocation, UncertaintyContainer.class);
		
		var defaultInfoSource = uc.getSources().stream().findFirst().get();
		// X UC -> create a Information source, that has a fis with only one output value...
		// X DDC -> Add enumeration with a single default trust value
		// X DDC -> For each CharacteristicType -> create a new TrustedEnumCharType, with exact same properties but with default trust enum, Map previous id with new exchanged Id
		// X DDC -> for Each behavior -> if there is an assignment with a EnumCharacteristicReference, create a new Assignment with a TrustedEnumCharacteristicReference and remove the old ones
		// DFD -> for Each Characteristic -> create a new TrustedEnumCharacteristic, with exact same properties, but with new TrustedEnumCharType and default information source
		// DFD -> for each behavior -> see two above
		
		
		this.defaultTrustLiteral = DataDictionaryCharacterizedFactory.eINSTANCE.createLiteral();
		this.defaultTrustLiteral.setName(defaultInfoSource.getTrustSystem().getOutput().getName());
		this.defaultTrustEnum = DataDictionaryCharacterizedFactory.eINSTANCE.createEnumeration();
		this.defaultTrustEnum.setName("DefaultTrust");
		this.defaultTrustEnum.getLiterals().add(defaultTrustLiteral);
		defaultTrustLiteral.setEnum(this.defaultTrustEnum);
		ddc.getEnumerations().add(this.defaultTrustEnum);
		
		this.trustedCharTypes = new ArrayList<TrustedEnumCharacteristicType>();
		
		ddc.getCharacteristicTypes().forEach(type -> {
			if(type instanceof EnumCharacteristicType) {
				var enumCharType = (EnumCharacteristicType) type;
				var trustedType = UncertaintyFactory.eINSTANCE.createTrustedEnumCharacteristicType();
				this.trustedCharTypes.add(trustedType);
				trustedType.setId(enumCharType.getId());
				trustedType.setName(enumCharType.getName());
				trustedType.setTrust(this.defaultTrustEnum);
				trustedType.setType(enumCharType.getType());
			}
			
		});
		
		ddc.getBehaviorDefinitions().forEach(behavior -> {
			behavior.getAssignments().forEach(assignment -> {
				var trustedCharRefLhs = createTrustedDataCharReference(assignment.getLhs());
				assignment.setLhs(trustedCharRefLhs);
				
				var trustedRhs = createAndIterateTrustedTerm(assignment.getRhs());
				assignment.setRhs(trustedRhs);
			});
		});
	}
	
	private TrustedDataCharacteristicReference createTrustedDataCharReference(DataCharacteristicReference ref) {
		var trustedCharRef = UncertaintyFactory.eINSTANCE.createTrustedDataCharacteristicReference();
		var trustedCharType = getTrustedCharTypeWithId(ref.getCharacteristicType().getId());
		trustedCharRef.setCharacteristicType(trustedCharType);
		trustedCharRef.setId(ref.getId());
		trustedCharRef.setLiteral(ref.getLiteral());
		trustedCharRef.setPin(ref.getPin());
		trustedCharRef.setTrust(this.defaultTrustLiteral);
		return trustedCharRef;
	}
	
	private TrustedContainerCharacteristicReference createTrustedDataCharReference(ContainerCharacteristicReference ref) {
		var trustedCharRef = UncertaintyFactory.eINSTANCE.createTrustedContainerCharacteristicReference();
		var trustedCharType = getTrustedCharTypeWithId(ref.getCharacteristicType().getId());
		trustedCharRef.setCharacteristicType(trustedCharType);
		trustedCharRef.setId(ref.getId());
		trustedCharRef.setLiteral(ref.getLiteral());
		trustedCharRef.setTrust(this.defaultTrustLiteral);
		return trustedCharRef;
	}
	
	private TrustedEnumCharacteristicType getTrustedCharTypeWithId(String id) {
		var opt = this.trustedCharTypes.stream().filter(t -> t.getId() == id).findFirst();
		if(opt.isEmpty()) {
			return null;
		} else {
			return opt.get();
		}
	}
	
	private Term createAndIterateTrustedTerm(Term term) {
		if(term instanceof BinaryLogicTerm) {
			var binaryTerm = (BinaryLogicTerm) term;
			var left = createAndIterateTrustedTerm(binaryTerm.getLeft());
			var right = createAndIterateTrustedTerm(binaryTerm.getRight());
			binaryTerm.setLeft(left);
			binaryTerm.setRight(right);
		} else if(term instanceof UnaryLogicTerm) {
			var unaryTerm = (UnaryLogicTerm) term;
			var intTerm = createAndIterateTrustedTerm(unaryTerm.getTerm());
			unaryTerm.setTerm(intTerm);
		} else if(term instanceof DataCharacteristicReference) {
			return createTrustedDataCharReference((DataCharacteristicReference) term);
		} else if(term instanceof ContainerCharacteristicReference) {
			return createTrustedDataCharReference((ContainerCharacteristicReference) term);
		}
		
		// The term is a constant, nothing is changed
		return term;
	}

	@Override
	public void cleanup(IProgressMonitor monitor) throws CleanupFailedException {
		// TODO Auto-generated method stub

	}

	@Override
	public String getName() {
		return "Update DFD and DDC to trusted characteristics job";
	}

	private <T> T getSingleModelFromBlackboard(ModelLocation location, Class<T> class1) {
		var dfds = getBlackboard().getContents(location)
	            .stream()
	            .filter(class1::isInstance)
	            .map(class1::cast)
	            .collect(Collectors.toList());
        if (dfds.size() != 1) {
            new JobFailedException("There is not exactly one " + class1.getSimpleName() + " available.");
        }
        
        return dfds.get(0);
	}

}
