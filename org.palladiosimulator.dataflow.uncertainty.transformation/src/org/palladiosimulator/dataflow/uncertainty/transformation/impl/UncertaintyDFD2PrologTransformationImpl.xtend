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

class UncertaintyDFD2PrologTransformationImpl extends DFD2PrologTransformationImpl {
	
	val uncertaintyDFDFactory = UncertaintyFactory.eINSTANCE
	
	new(UniqueNameProvider nameProvider) {
		super(nameProvider)
	}
	
		initTransformationState(dfd)
		
		addPreamble(dfd)
		
		add(createHeaderComment("Characteristic types"))
		var charTypes = #[trustedCharacteristicTypesInBehaviors, trustedCharacteristicTypesInNodes].flatten.distinct
		charTypes.forEach[transformCharacteristicType.add]
		
		add(createHeaderComment("Nodes"))
		dfd.nodes.forEach[transformNode.add]
		
		if (!usedDataTypes.isEmpty) {
			add(createHeaderComment("Data Types"))
			usedDataTypes.forEach[transformDataType.add]
		}
		
		add(createHeaderComment("Edges"))
		dfd.edges.forEach[transformEdge.add]
		
		new TransformationResultImpl(program, trace)
	}
	
	protected override void initTransformationState(DataFlowDiagram dfd) {
		this.program = createProgram
		this.trace = new DFD2PrologTransformationWritableTraceImpl
		this.trace.add(dfd, program)
		this.stagedTraces.clear()
		this.trustedCharacteristicTypesInBehaviors = dfd.findAllTrustedCharacteristicTypesInBehaviors
		this.trustedCharacteristicTypesInNodes = dfd.findAllTrustedCharacteristicTypesInNodes
		this.usedDataTypes = dfd.findAllUsedDataTypes
	}
	
	interface TrustedOutputBehaviorCreator {	    
	    def Rule createTrustedOutputCharacteristicRule(CharacterizedNode node, Pin pin, TrustedEnumCharacteristicType ct, Literal value, Literal trust)
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