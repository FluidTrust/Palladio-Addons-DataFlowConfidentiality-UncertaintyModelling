package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.jobs;

import java.util.ArrayList;
import java.util.stream.Collectors;

import org.eclipse.core.runtime.IProgressMonitor;
import org.palladiosimulator.dataflow.Uncertainty.TrustedContainerCharacteristicReference;
import org.palladiosimulator.dataflow.Uncertainty.TrustedDataCharacteristicReference;
import org.palladiosimulator.dataflow.Uncertainty.TrustedEnumCharacteristic;
import org.palladiosimulator.dataflow.Uncertainty.TrustedEnumCharacteristicType;
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyContainer;
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyFactory;
import org.palladiosimulator.dataflow.confidentiality.transformation.workflow.blackboards.KeyValueMDSDBlackboard;
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram;
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedNode;
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.Assignment;
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.DataDictionaryCharacterized;
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.DataDictionaryCharacterizedFactory;
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.EnumCharacteristic;
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
		this.ucLocation = ucLocation;
	}

	@Override
	public void execute(IProgressMonitor monitor) throws JobFailedException, UserCanceledException {
		monitor.beginTask(getName(), 1);
		
		var dfd = getSingleModelFromBlackboard(dfdLocation, DataFlowDiagram.class);
		var ddc = getSingleModelFromBlackboard(ddcLocation, DataDictionaryCharacterized.class);
		var uc = getSingleModelFromBlackboard(ucLocation, UncertaintyContainer.class);
		
		var defaultInfoSource = uc.getSources().stream().findFirst().get();
		
		// 1. UC -> create a Information source, that has a fis with only one output value
		this.defaultTrustLiteral = DataDictionaryCharacterizedFactory.eINSTANCE.createLiteral();
		// the defaultInfoSource output has only one membership function, which is defined as mf(x) = 1
		this.defaultTrustLiteral.setName(defaultInfoSource.getTrustSystem().getOutput().getTerm().get(0).getName());
		this.defaultTrustEnum = DataDictionaryCharacterizedFactory.eINSTANCE.createEnumeration();
		this.defaultTrustEnum.setName("DefaultTrust");
		this.defaultTrustEnum.getLiterals().add(defaultTrustLiteral);
		defaultTrustLiteral.setEnum(this.defaultTrustEnum);
		
		if(ddc != null) {
			// 2. DDC -> Add enumeration with a single default trust value
			ddc.getEnumerations().add(this.defaultTrustEnum);
			
			this.trustedCharTypes = new ArrayList<TrustedEnumCharacteristicType>();
			
			// 3. DDC -> For each CharacteristicType, create a new TrustedEnumCharType, 
			// with exact same properties and default trust enum; Map previous id with new exchanged Id
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
			
			ddc.getCharacteristicTypes().clear();
			ddc.getCharacteristicTypes().addAll(trustedCharTypes);
			
			// 4. DDC -> for Each behavior, if there is an assignment with a EnumCharacteristicReference, 
			// for each Assignment, create a new with a TrustedEnumCharacteristicReference and exchange for the old ones
			ddc.getBehaviorDefinitions().forEach(behavior -> {
				behavior.getAssignments().forEach(assignment -> modifyAssignment(assignment));
			});
		}
		
		if(dfd != null) {
			// 5. DFD -> for Each Characteristic, create a new TrustedEnumCharacteristic, 
			// copy properties of original EnumCharacteristic, add new TrustedEnumCharType and default information source
			dfd.getNodes().forEach(node -> {
				if(node instanceof CharacterizedNode) {
					var charNode = (CharacterizedNode)node;
					var trustedChars = new ArrayList<TrustedEnumCharacteristic>();
					var replacedChars = new ArrayList<EnumCharacteristic>();
					charNode.getCharacteristics().forEach(characteristic -> {
						if(characteristic instanceof EnumCharacteristic) {
							var enumChar = (EnumCharacteristic) characteristic;
							var trustedChar = UncertaintyFactory.eINSTANCE.createTrustedEnumCharacteristic();
							trustedChar.setId(enumChar.getId());
							trustedChar.setName(enumChar.getName());
							trustedChar.getValues().addAll(enumChar.getValues());
							trustedChar.setTrustSource(defaultInfoSource);
							trustedChar.setType(getTrustedCharTypeWithId(enumChar.getType().getId()));
							trustedChars.add(trustedChar);
							replacedChars.add(enumChar);
						}
					});
					
					// Remove all EnumCharacteristics, that have been replaces with trusted ones
					charNode.getOwnedCharacteristics().removeAll(replacedChars);
					charNode.getReferencedCharacteristics().removeAll(replacedChars);
					charNode.getOwnedCharacteristics().addAll(trustedChars);
//					charNode.getCharacteristics().removeAll(replacedChars);
//					charNode.getCharacteristics().addAll(trustedChars);
					
					// 6. DFD -> if a CharacterizedNode has a owned behavior (defined in the dfd and not the ddc),
					// do the same as for the BehaviorDefinitions defined in the ddc.
					if(charNode.getOwnedBehavior() != null) {
						charNode.getOwnedBehavior().getAssignments().forEach(assignment -> modifyAssignment(assignment));
					}
					
					if(charNode.getReferencedBehavior() != null) {
						charNode.getReferencedBehavior().getAssignments().forEach(assignment -> modifyAssignment(assignment));
					}
				}
			});
		}
		monitor.worked(1);
		monitor.done();
	}
	
	private void modifyAssignment(Assignment assignment) {
		// left side of an assignment is always of the typ DataCharacteristicReference
		var trustedCharRefLhs = createTrustedDataCharReference(assignment.getLhs());
		assignment.setLhs(trustedCharRefLhs);
		
		// right side can vary and recursively iterated
		var trustedRhs = createAndIterateTrustedTerm(assignment.getRhs());
		assignment.setRhs(trustedRhs);
	}
	
	private TrustedDataCharacteristicReference createTrustedDataCharReference(DataCharacteristicReference ref) {
		var trustedCharRef = UncertaintyFactory.eINSTANCE.createTrustedDataCharacteristicReference();
		if(ref.getCharacteristicType() != null) {
			var trustedCharType = getTrustedCharTypeWithId(ref.getCharacteristicType().getId());
			trustedCharRef.setCharacteristicType(trustedCharType);
			if(ref.getLiteral() != null) {
				trustedCharRef.setLiteral(getFittingLiteralFromTrustedCharType(trustedCharType, ref.getLiteral()));
			}
			trustedCharRef.setTrust(this.defaultTrustLiteral);
		}
		
		trustedCharRef.setId(ref.getId());
		trustedCharRef.setPin(ref.getPin());
		return trustedCharRef;
	}
	
	private TrustedContainerCharacteristicReference createTrustedContainerCharReference(ContainerCharacteristicReference ref) {
		var trustedCharRef = UncertaintyFactory.eINSTANCE.createTrustedContainerCharacteristicReference();
		if(ref.getCharacteristicType() != null) {
			var trustedCharType = getTrustedCharTypeWithId(ref.getCharacteristicType().getId());
			trustedCharRef.setCharacteristicType(trustedCharType);
			if(ref.getLiteral() != null) {
				trustedCharRef.setLiteral(getFittingLiteralFromTrustedCharType(trustedCharType, ref.getLiteral()));
			}
			trustedCharRef.setTrust(this.defaultTrustLiteral);
		}
		
		trustedCharRef.setId(ref.getId());
		return trustedCharRef;
	}
	
	private TrustedEnumCharacteristicType getTrustedCharTypeWithId(String id) {
		for(var trustedType : this.trustedCharTypes ) {
			if(trustedType.getId().equals(id)) {
				return trustedType;
			}
		}
		return null;
	}
	
	private Literal getFittingLiteralFromTrustedCharType(TrustedEnumCharacteristicType type, Literal oldLiteral) {
		for(var newLiteral : type.getType().getLiterals()) {
			if(newLiteral.getId().equals(oldLiteral.getId())) {
				return newLiteral;
			}
		}
		return null;
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
			return createTrustedContainerCharReference((ContainerCharacteristicReference) term);
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

	private <S> S getSingleModelFromBlackboard(ModelLocation location, Class<S> class1) throws JobFailedException {
		var dfds = getBlackboard().getContents(location)
	            .stream()
	            .filter(class1::isInstance)
	            .map(class1::cast)
	            .collect(Collectors.toList());
        if (dfds.size() != 1) {
            throw new JobFailedException("There is not exactly one " + class1.getSimpleName() + " available.");
        }
        
        return dfds.get(0);
	}
}