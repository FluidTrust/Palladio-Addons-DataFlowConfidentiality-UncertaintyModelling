package org.palladiosimulator.dataflow.uncertainty.transformation.impl

import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.impl.DFD2PrologTransformationImpl
import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.naming.UniqueNameProvider
import org.palladiosimulator.dataflow.Uncertainty.TrustedEnumCharacteristicType
import java.util.ArrayList
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedNode
import org.palladiosimulator.supporting.prolog.model.prolog.Rule
import org.palladiosimulator.supporting.prolog.model.prolog.expressions.Expression
import org.palladiosimulator.supporting.prolog.model.prolog.Clause
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedStore
import org.palladiosimulator.dataflow.Uncertainty.TrustedDataCharacteristicReference
import org.palladiosimulator.dataflow.Uncertainty.TrustedContainerCharacteristicReference
import org.palladiosimulator.dataflow.Uncertainty.TrustedEnumCharacteristic
import org.palladiosimulator.dataflow.uncertainty.fis.SourceTrustEvaluator
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.MembershipFunction
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyFactory
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedActorProcess
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.Entity
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.EnumCharacteristicType
import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.impl.DFD2PrologTransformationImpl.DFD2PrologOutputBehaviorCreator
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedProcess
import java.util.Optional
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.Assignment
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.Literal
import java.util.List
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.Pin
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.expressions.EnumCharacteristicReference
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.expressions.Term
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedExternalActor

class UncertaintyDFD2PrologTransformationImpl extends DFD2PrologTransformationImpl {
	
	val uncertaintyDFDFactory = UncertaintyFactory.eINSTANCE
	
	new(UniqueNameProvider nameProvider) {
		super(nameProvider)
	}
	
	interface UncertaintyDFD2PrologOutputBehaviorCreator {
		def Rule createOutputCharacteristicRule(UncertaintyDFD2PrologTransformationParameter param)
	}
	
	protected def dispatch transformCharacteristicType(TrustedEnumCharacteristicType characteristicType) {
		val facts = new ArrayList
		facts += _transformCharacteristicType(characteristicType as EnumCharacteristicType)
		
		for (var i = 0; i < characteristicType.trust.literals.size; i++) {
			val trustLiteral = characteristicType.trust.literals.get(i)
			facts += createFact(createCompoundTerm("characteristicTypeTrust", characteristicType.uniqueQuotedString, trustLiteral.uniqueQuotedString, i.toInt))
			stageTrace(facts.last, [trace.add(trustLiteral, trustLiteral.uniqueQuotedString.value)])
		}
		
		facts
	}
	
	protected override dispatch transformNode(CharacterizedStore store) {
		store.transformNodeWithUncertainty("store", new UncertaintyDFD2PrologOutputBehaviorCreator() {
			
			override createOutputCharacteristicRule(UncertaintyDFD2PrologTransformationParameter param) {
				// the flow tree has to be bound before the assignments can use them because the assignment
				// could be a pure negation, which is not able to bind a valid flow stack.
				val flowClauses = new ArrayList<Expression>(createFlowTreeClauses(param.node, param.node.behavior.inputs))
				val term = uncertaintyDFDFactory.createTrustedDataCharacteristicReference
				term.pin = param.node.behavior.inputs.get(0)
				term.characteristicType = param.ct
				term.literal = param.l 
				term.trust = param.t
				flowClauses += term.transformAssignmentTerm(param)
				createRule(
					createCharacteristicTerm(param.node, param, "S".toVar, "VISITED".toVar),
					createConjunction(flowClauses)
				)
			}
		})
	}
	
	protected override dispatch transformNode(CharacterizedProcess process) {
		process.transformNodeWithUncertainty("process", new UncertaintyDFD2PrologOutputBehaviorCreator() {
			
			override createOutputCharacteristicRule(UncertaintyDFD2PrologTransformationParameter param) {
				val assignmentToTransform = param.node.behavior.assignments.findLastMatchingAssignment(param.pin, param.ct as TrustedEnumCharacteristicType, param.l, param.t)
				val transformedAssignment = assignmentToTransform.transformAssignment(param)
				val needsFlowTree = assignmentToTransform.needsFlowTree
				if (needsFlowTree) {
					// the flow tree has to be bound before the assignments can use them because the assignment
					// could be a pure negation, which is not able to bind a valid flow stack.
					val flowClauses = new ArrayList<Expression>(createFlowTreeClauses(param.node, param.node.behavior.inputs))
					flowClauses += transformedAssignment
					createRule(
						createCharacteristicTerm(process, param, "S".toVar, "VISITED".toVar),
						createConjunction(flowClauses)
					)
				} else {
					val fsVar = process.needsEmptyFlowTree ? createList : "_".toVar
					createRule(
						createCharacteristicTerm(process, param, fsVar, "_".toVar),
						createConjunction(transformedAssignment)
					)
				}
			}
		})
	}
	
	protected override dispatch transformNode(CharacterizedExternalActor actor) {
		actor.transformNodeWithUncertainty("actor", new UncertaintyDFD2PrologOutputBehaviorCreator() {
			
			override createOutputCharacteristicRule(UncertaintyDFD2PrologTransformationParameter param) {
				val assignmentToTransform = param.node.behavior.assignments.findLastMatchingAssignment(param.pin, param.ct as TrustedEnumCharacteristicType, param.l, param.t)
				if (assignmentToTransform.needsFlowTree) {
					throw new IllegalArgumentException("Actors must not refer to input pins in their behavior.")
				} else {
					createRule(
						createCharacteristicTerm(param.node, param, createList, "_".toVar),
						createConjunction(assignmentToTransform.transformAssignment(param))
					)
				}
			}	
		})
	}
	
	// has to be copied in order to call the correct _transformNode...
	protected override dispatch transformNode(CharacterizedActorProcess process) {
		val clauses = new ArrayList<Clause>
		clauses += createFact(createCompoundTerm("actorProcess", (process as CharacterizedNode).uniqueQuotedString, process.actor.uniqueQuotedString))
		clauses += (process as CharacterizedProcess)._transformNode
		clauses
	}
	
	protected static def Optional<Assignment> findLastMatchingAssignment(List<Assignment> assignments, Pin pin,
            TrustedEnumCharacteristicType ct, Literal l, Literal t) {
        for (assignment : assignments.reverseView) {
			if (isMatchingAssignment(assignment, pin, ct, l, t)) {
				return Optional.of(assignment);
			}
        }
        // there is no matching assignment
        return Optional.empty();
    }
    
    protected static def isMatchingAssignment(Assignment assignment, Pin pin, TrustedEnumCharacteristicType ct, Literal l, Literal t) {
    	var lhs = assignment.getLhs() as TrustedDataCharacteristicReference
           
        // trust does not match
        if (lhs.trust !== null && lhs.trust !== t) {
			return false
		}
		
		// check original matching
		isMatchingAssignment(assignment, pin, ct, l)
    }
    
    protected static def dispatch boolean isRhsTermCompatible(TrustedDataCharacteristicReference term, TrustedEnumCharacteristicType ct) {
    	var termCharacteristicType = term.characteristicType as TrustedEnumCharacteristicType
        var termLiteral = term.literal
        var termTrust = term.trust
        
        // case 0: only wildcards except for trust -> incompatible (characteristic type has to be compatbile)
        if (termCharacteristicType === null && termLiteral === null && termTrust !== null) {
            return false;
        }
        
    	// case 1: only trust wildcard -> characteristic type has to be compatbile
        if (termCharacteristicType !== null && termLiteral !== null && termTrust === null 
                && termCharacteristicType.getType() == ct.getType()) {
            return true;
        }

    	// case 2: Check compatibility based on original definition
    	isRhsTermCompatible(term, ct)
    }
    
    protected static def dispatch boolean isRhsTermCompatible(TrustedContainerCharacteristicReference term, TrustedEnumCharacteristicType ct) {
    	var termCharacteristicType = term.characteristicType as TrustedEnumCharacteristicType
        var termLiteral = term.literal
        var termTrust = term.trust
        
        // case 0: only wildcards except for trust -> incompatible (characteristic type has to be compatbile)
        if (termCharacteristicType === null && termLiteral === null && termTrust !== null) {
            return false;
        }
        
    	// case 1: only trust wildcard -> characteristic type has to be compatbile
        if (termCharacteristicType !== null && termLiteral !== null && termTrust === null 
                && termCharacteristicType.getType() == ct.getType()) {
            return true;
        }
        
        // case 2: Check compatibility based on original definition
    	isRhsTermCompatible(term, ct)
    }
	
	protected override transformNode(CharacterizedNode node, String factName, DFD2PrologOutputBehaviorCreator outputBehaviorCreator) {
		this.transformNodeWithUncertainty(node, factName, new UncertaintyDFD2PrologOutputBehaviorCreator() {
			
			override createOutputCharacteristicRule(UncertaintyDFD2PrologTransformationParameter param) {
				outputBehaviorCreator.createOutputCharacteristicRule(param)
			}
		})
	}
	
	protected def transformNodeWithUncertainty(CharacterizedNode node, String factName, UncertaintyDFD2PrologOutputBehaviorCreator outputBehaviorCreator) {
		val clauses = new ArrayList<Clause>
		
		// type-specific fact
		clauses += createComment('''«factName.toFirstUpper» «(node as Entity).name»''')
		clauses += createFact(createCompoundTerm(factName, node.uniqueQuotedString))
		clauses.last.stageTrace[trace.add(node as Entity, node.uniqueQuotedString.value)]
		
		// node characteristics
		node.characteristics.filter(TrustedEnumCharacteristic).forEach[characteristic |
			// evaluate the certainty value and get the fitting enum literal
			val trust = SourceTrustEvaluator.evaluate(characteristic.trustSource).getLiteralForMembershipFunction(characteristic.trustedEnumCharacteristicType)
			characteristic.values.forEach[literal |
				clauses += createFact(createNodeCharacteristicTerm(new UncertaintyDFD2PrologTransformationParameter(node, characteristic.trustedEnumCharacteristicType, literal, trust)))
			]
		]
		
		// behavior
		node.behavior.inputs.forEach[pin |
			clauses += createFact(createCompoundTerm("inputPin", node.uniqueQuotedString, pin.getUniqueQuotedString(node)))
			clauses.last.stageTrace[trace.add(node, pin, pin.getUniqueQuotedString(node).value)]
		]
		node.behavior.outputs.forEach[pin |
			clauses += createFact(createCompoundTerm("outputPin", node.uniqueQuotedString, pin.getUniqueQuotedString(node)))
			clauses.last.stageTrace[trace.add(node, pin, pin.getUniqueQuotedString(node).value)]
			characteristicTypesInBehaviors.forEach[ct |
				if(ct instanceof TrustedEnumCharacteristicType) {
					val trustedCt = ct as TrustedEnumCharacteristicType
					trustedCt.type.literals.forEach[l |
					trustedCt.trust.literals.forEach[t | 
						clauses += outputBehaviorCreator.createOutputCharacteristicRule(
							new UncertaintyDFD2PrologTransformationParameter(node, pin, trustedCt, l, t)
						)
						]
					]
				}
			]
		]
		
		clauses
	}
	
	protected override void addCharacteristicHelper(DataFlowDiagram dfd) {
		add(createHeaderComment("HELPER: Shortcuts for common use cases"))
		add(createComment("Shortcut for characteristic queries"))
		add(createRule(
			createCompoundTerm("characteristic", "N", "PIN", "CT", "V", "T", "S"),
			createCompoundTerm("characteristic", "N".toVar, "PIN".toVar, "CT".toVar, "V".toVar, "T".toVar, "S".toVar, createList)
		))
		
		if (!dfd.nodes.filter(CharacterizedActorProcess).empty) {
			add(createComment("Always inherit node characteristics from parent"))
			add(createRule(
				createCompoundTerm("nodeCharacteristic", "N", "CT", "V", "T"),
				createConjunction(
					createCompoundTerm("actorProcess", "N", "A"),
					createCompoundTerm("nodeCharacteristic", "A", "CT", "V", "T")
				)
			))			
		}
		
		add(createHeaderComment("HELPER: collect all available data characteristics"))
		add(createRule(
			createCompoundTerm("setof_characteristics", "N", "PIN", "CT", "RESULT", "T","S"),
			createConjunction(
				createCompoundTerm("flowTree", "N".toVar, "PIN".toVar, "S".toVar),
				createCompoundTerm("setof", "V".toVar, createCompoundTerm("characteristic", "N", "PIN", "CT", "V", "T", "S"), "RESULT".toVar)
			)
		))
		
		add(createHeaderComment("HELPER: collect all available data characteristics that have a specific trust value"))
		add(createRule(
			createCompoundTerm("setof_characteristics_with_trust", "N", "PIN", "CT", "RESULT", "T", "S"),
			createConjunction(
				createCompoundTerm("flowTree", "N".toVar, "PIN".toVar, "S".toVar),
				createCompoundTerm("setof", "V".toVar, createCompoundTerm("characteristic", "N", "PIN", "CT", "V", "T", "S"), "RESULT".toVar)
			)
		))
		
		// TODO: Remove this rule if not needed for queries
		add(createHeaderComment("HELPER: collect all available trust values for a specific data characteristic value"))
		add(createRule(
			createCompoundTerm("setof_characteristic_trust", "N", "PIN", "CT", "V", "RESULT", "S"),
			createConjunction(
				createCompoundTerm("flowTree", "N".toVar, "PIN".toVar, "S".toVar),
				createCompoundTerm("setof", "T".toVar, createCompoundTerm("characteristic", "N", "PIN", "CT", "V", "T", "S"), "RESULT".toVar)
			)
		))
		
		// TODO: Remove this rule if not needed for queries
		add(createHeaderComment("HELPER: collects all characteristic trusts and compares if there is no match in trust values"))
		add(createRule(
			createCompoundTerm("nomatch", "P", "PIN", "NODECHARTYPE", "DATACHARTYPE", "S", "V"), 
			createConjunction(
				createCompoundTerm("setof", "T1".toVar, createCompoundTerm("nodeCharacteristic", "P", "NODECHARTYPE", "V", "T1"), "NODETRUST".toVar),
				createCompoundTerm("setof_characteristic_trust", "P", "PIN", "DATACHARTYPE", "V", "DATATRUST", "S"),
				createCompoundTerm("intersection", "NODETRUST".toVar, "DATATRUST".toVar, createList(#[]))
			)
		))
		
		add(createHeaderComment("HELPER: find input characteristics"))
		add(createRule(
			createCompoundTerm("characteristic", "N".toVar, "PIN".toVar, "CT".toVar, "V".toVar, "T".toVar, createList(#["F"], #["S"]), "VISITED".toVar),
			createConjunction(
				createCompoundTerm("inputPin", "N", "PIN"),
				createCompoundTerm("dataflow", "F", "NSRC", "PINSRC", "N", "PIN"),
				createCompoundTerm("intersection", createList(#["F"]), "VISITED".toVar, createList),
				createCompoundTerm("characteristic", "NSRC".toVar, "PINSRC".toVar, "CT".toVar, "V".toVar, "T".toVar, "S".toVar, createList(#["F"], #["VISITED"]))
			)
		))
	}
	
	protected def dispatch Expression transformAssignmentTerm(TrustedDataCharacteristicReference rhs, UncertaintyDFD2PrologTransformationParameter param) {
		var referencedCharacteristicType = rhs.characteristicType as TrustedEnumCharacteristicType ?: param.trustedCt
		var referencedLiteral = rhs.literal ?: param.l
		var referencedTrust = rhs.trust ?: param.t
		var treeVariable = '''S«param.node.behavior.inputs.indexOf(rhs.pin)»'''
		createCharacteristicTerm(param.node, new UncertaintyDFD2PrologTransformationParameter(param.node, rhs.pin, referencedCharacteristicType, referencedLiteral, referencedTrust), treeVariable.toVar, "VISITED".toVar)
	}
	
	protected def dispatch Expression transformAssignmentTerm(TrustedContainerCharacteristicReference rhs, UncertaintyDFD2PrologTransformationParameter param) {
		var referencedCharacteristicType = rhs.characteristicType as TrustedEnumCharacteristicType ?: param.trustedCt
		var referencedLiteral = rhs.literal ?: param.l
		var referencedTrust = rhs.trust ?: param.t
		createNodeCharacteristicTerm(new UncertaintyDFD2PrologTransformationParameter(param.node, referencedCharacteristicType, referencedLiteral, referencedTrust))
	}
	
	private def getLiteralForMembershipFunction(MembershipFunction funct, TrustedEnumCharacteristicType ct) {
		ct.trust.literals.findFirst[l| l.name.equals(funct.name)]
	}
	
	protected def dispatch createCharacteristicTerm(CharacterizedNode node, UncertaintyDFD2PrologTransformationParameter param, Expression s, Expression visited) {
		createCompoundTerm("characteristic", param.node.uniqueQuotedString, param.pin.getUniqueQuotedString(node), param.ct.uniqueQuotedString, param.l.uniqueQuotedString, param.t.uniqueQuotedString, s, visited)
	}
	
	protected def dispatch createNodeCharacteristicTerm(UncertaintyDFD2PrologTransformationParameter param) {
		createCompoundTerm("nodeCharacteristic", param.node.uniqueQuotedString, param.ct.uniqueQuotedString, param.l.uniqueQuotedString, param.t.uniqueQuotedString)
	}
}
