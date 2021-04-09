package org.palladiosimulator.dataflow.uncertainty.transformation.impl

import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.impl.DFD2PrologTransformationImpl
import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.naming.UniqueNameProvider
import org.palladiosimulator.dataflow.Uncertainty.TrustedEnumCharacteristicType
import java.util.ArrayList
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.Literal
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.Pin
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedNode
import org.palladiosimulator.supporting.prolog.model.prolog.Rule
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedProcess
import org.palladiosimulator.supporting.prolog.model.prolog.expressions.Expression
import org.palladiosimulator.supporting.prolog.model.prolog.Clause
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.Entity
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedExternalActor
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedStore
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.Assignment
import java.util.Optional
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.expressions.True
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.expressions.False
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.expressions.Or
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.expressions.And
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.expressions.Not
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.Node
import org.palladiosimulator.dataflow.Uncertainty.TrustedDataCharacteristicReference
import org.palladiosimulator.dataflow.Uncertainty.TrustedContainerCharacteristicReference
import org.palladiosimulator.dataflow.Uncertainty.TrustedEnumCharacteristic
import org.palladiosimulator.dataflow.uncertainty.fis.SourceTrustEvaluator
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.MembershipFunction
import org.palladiosimulator.dataflow.Uncertainty.UncertaintyFactory
import org.palladiosimulator.dataflow.diagram.DataFlowDiagram.DataFlowDiagram
import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.impl.TransformationResultImpl
import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.impl.DFD2PrologTransformationWritableTraceImpl
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedActorProcess

class UncertaintyDFD2PrologTransformationImpl extends DFD2PrologTransformationImpl {
	
	val uncertaintyDFDFactory = UncertaintyFactory.eINSTANCE
	protected var Iterable<TrustedEnumCharacteristicType> trustedCharacteristicTypesInBehaviors
	protected var Iterable<TrustedEnumCharacteristicType> trustedCharacteristicTypesInNodes
	
	new(UniqueNameProvider nameProvider) {
		super(nameProvider)
	}
	
	override transform(DataFlowDiagram dfd) {
		initTransformationState(dfd)
		
		addPreamble(dfd)
		
		add(createHeaderComment("Characteristic types"))
		var charTypes = #[trustedCharacteristicTypesInBehaviors, trustedCharacteristicTypesInNodes].flatten.distinct as Iterable<TrustedEnumCharacteristicType>
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
	}
	
	protected def dispatch transformCharacteristicType(TrustedEnumCharacteristicType characteristicType) {
		val facts = new ArrayList
		facts += createFact(createCompoundTerm("characteristicType", characteristicType.uniqueQuotedString))
		facts.last.stageTrace[trace.add(characteristicType, characteristicType.uniqueQuotedString.value)]
		for (var i = 0; i < characteristicType.type.literals.size; i++) {
			val literal = characteristicType.type.literals.get(i)
			facts += createFact(createCompoundTerm("characteristicTypeValue", characteristicType.uniqueQuotedString, literal.uniqueQuotedString, i.toInt))
			stageTrace(facts.last, [trace.add(literal, literal.uniqueQuotedString.value)])
		}
		
		for (var i = 0; i < characteristicType.trust.literals.size; i++) {
			val trustLiteral = characteristicType.trust.literals.get(i)
			facts += createFact(createCompoundTerm("characteristicTypeTrust", characteristicType.uniqueQuotedString, trustLiteral.uniqueQuotedString, i.toInt))
			stageTrace(facts.last, [trace.add(trustLiteral, trustLiteral.uniqueQuotedString.value)])
		}
		
		facts
	}
	
	protected override dispatch transformNode(CharacterizedProcess process) {
		process.transformNode("process", [node, pin, ct, l, t |
			val assignmentToTransform = node.behavior.assignments.findLastMatchingAssignment(pin, ct, l)
			val transformedAssignment = assignmentToTransform.transformAssignment(node, pin, ct, l, t)
			val needsFlowTree = assignmentToTransform.needsFlowTree
			if (needsFlowTree) {
				val flowClauses = new ArrayList<Expression>(createFlowTreeClauses(node, node.behavior.inputs))
				flowClauses += transformedAssignment
				createRule(
					createCompoundTerm("characteristic", node.uniqueQuotedString, pin.getUniqueQuotedString(process as Node), ct.uniqueQuotedString, l.uniqueQuotedString, t.uniqueQuotedString, "S".toVar, "VISITED".toVar),
					createConjunction(flowClauses)
				)
			} else {
				val fsVar = process.needsEmptyFlowTree ? createList : "_".toVar
				createRule(
					createCompoundTerm("characteristic", node.uniqueQuotedString, pin.getUniqueQuotedString(process as Node), ct.uniqueQuotedString, l.uniqueQuotedString, t.uniqueQuotedString, fsVar, "_".toVar),
					createConjunction(transformedAssignment)
				)
			}
		])
	}
	
	protected override dispatch transformNode(CharacterizedExternalActor actor) {
		actor.transformNode("actor", [node, pin, ct, l, t|
			val assignmentToTransform = node.behavior.assignments.findLastMatchingAssignment(pin, ct, l)
			if (assignmentToTransform.needsFlowTree) {
				throw new IllegalArgumentException("Actors must not refer to input pins in their behavior.")
			} else {
				createRule(
					createCompoundTerm("characteristic", node.uniqueQuotedString, pin.getUniqueQuotedString(node), ct.uniqueQuotedString, l.uniqueQuotedString, t.uniqueQuotedString, createList, "_".toVar),
					createConjunction(assignmentToTransform.transformAssignment(node, pin, ct, l, t))
				)
			}
		])
	}
	
	protected override dispatch transformNode(CharacterizedStore store) {
		store.transformNode("store", [node, pin, ct, l, t|
				val flowClauses = new ArrayList<Expression>(createFlowTreeClauses(node, node.behavior.inputs))
				val term = uncertaintyDFDFactory.createTrustedDataCharacteristicReference
				term.pin = node.behavior.inputs.get(0)
				term.characteristicType = ct
				term.literal = l
				term.trust = t
				flowClauses += term.transformAssignmentTerm(node, pin, ct, l, t)
				createRule(
					createCompoundTerm("characteristic", node.uniqueQuotedString, pin.getUniqueQuotedString(node), ct.uniqueQuotedString, l.uniqueQuotedString, t.uniqueQuotedString, "S".toVar, "VISITED".toVar),
					createConjunction(flowClauses)
				)
		])
	}
	
	protected def transformNode(CharacterizedNode node, String factName, TrustedOutputBehaviorCreator outputBehaviorCreator) {
		val clauses = new ArrayList<Clause>
		
		// type-specific fact
		clauses += createComment('''«factName.toFirstUpper» «(node as Entity).name»''')
		clauses += createFact(createCompoundTerm(factName, node.uniqueQuotedString))
		clauses.last.stageTrace[trace.add(node as Entity, node.uniqueQuotedString.value)]
		
		// node characteristics
		node.characteristics.filter(TrustedEnumCharacteristic).forEach[characteristic |
			val trust = SourceTrustEvaluator.evaluate(characteristic.trustSource).getLiteralForMembershipFunction(characteristic.trustedEnumCharacteristicType)
			characteristic.values.forEach[literal |
				clauses += createFact(createCompoundTerm("nodeCharacteristic", node.uniqueQuotedString, characteristic.type.uniqueQuotedString, literal.uniqueQuotedString, trust.uniqueQuotedString))
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
			trustedCharacteristicTypesInBehaviors.forEach[ct |
				ct.type.literals.forEach[l |
					ct.trust.literals.forEach[t | 
						clauses += outputBehaviorCreator.createTrustedOutputCharacteristicRule(node, pin, ct, l, t)
						
					]
				]
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
			createCompoundTerm("setof_characteristics", "N", "PIN", "CT", "RESULT", "S"),
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
		
		// needed?
		add(createHeaderComment("HELPER: collect all available trust values for a specific data characteristic"))
		add(createRule(
			createCompoundTerm("setof_characteristic_trust", "N", "PIN", "CT", "V", "RESULT", "S"),
			createConjunction(
				createCompoundTerm("flowTree", "N".toVar, "PIN".toVar, "S".toVar),
				createCompoundTerm("setof", "T".toVar, createCompoundTerm("characteristic", "N", "PIN", "CT", "V", "T", "S"), "RESULT".toVar)
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
	
	
		/**
	 * Transforms the right hand side of an assignment to an expression. 
	 */
	protected def Expression transformAssignment(Optional<Assignment> assignment, CharacterizedNode node, Pin pin, TrustedEnumCharacteristicType ct, Literal value, Literal trust) {
		assignment.map[rhs.transformAssignmentTerm(node, pin, ct, value, trust)].orElse(createFalse)
	}
	
	protected def dispatch Expression transformAssignmentTerm(True rhs, CharacterizedNode node, Pin pin, TrustedEnumCharacteristicType ct, Literal value, Literal trust) {
		createTrue
	}
	
	protected def dispatch Expression transformAssignmentTerm(False rhs, CharacterizedNode node, Pin pin, TrustedEnumCharacteristicType ct, Literal value, Literal trust) {
		createFalse
	}
	
	protected def dispatch Expression transformAssignmentTerm(Or rhs, CharacterizedNode node, Pin pin, TrustedEnumCharacteristicType ct, Literal value, Literal trust) {
		createLogicalOr => [
			left = rhs.left.transformAssignmentTerm(node, pin, ct, value, trust)
			right = rhs.right.transformAssignmentTerm(node, pin, ct, value, trust)
		]
	}
	
	protected def dispatch Expression transformAssignmentTerm(And rhs, CharacterizedNode node, Pin pin, TrustedEnumCharacteristicType ct, Literal value, Literal trust) {
		createLogicalAnd => [
			left = rhs.left.transformAssignmentTerm(node, pin, ct, value, trust)
			right = rhs.right.transformAssignmentTerm(node, pin, ct, value, trust)
		]
	}
	
	protected def dispatch Expression transformAssignmentTerm(Not rhs, CharacterizedNode node, Pin pin, TrustedEnumCharacteristicType ct, Literal value, Literal trust) {
		createNotProvable => [
			expr = rhs.term.transformAssignmentTerm(node, pin, ct, value, trust)
		]
	}
	
	protected def dispatch Expression transformAssignmentTerm(TrustedDataCharacteristicReference rhs, CharacterizedNode node, Pin pin, TrustedEnumCharacteristicType ct, Literal value, Literal trust) {
		var referencedCharacteristicType = rhs.characteristicType ?: ct
		var referencedValue = rhs.literal ?: value
		var referencedTrust = rhs.trust ?: trust
		var treeVariable = '''S«node.behavior.inputs.indexOf(rhs.pin)»''' 
		createCompoundTerm(
			"characteristic",
			node.uniqueQuotedString,
			rhs.pin.getUniqueQuotedString(node),
			referencedCharacteristicType.uniqueQuotedString,
			referencedValue.uniqueQuotedString,
			referencedTrust.uniqueQuotedString,
			treeVariable.toVar,
			"VISITED".toVar
		)
	}
	
	protected def dispatch Expression transformAssignmentTerm(TrustedContainerCharacteristicReference rhs, CharacterizedNode node, Pin pin, TrustedEnumCharacteristicType ct, Literal value, Literal trust) {
		var referencedCharacteristicType = rhs.characteristicType ?: ct
		var referencedValue = rhs.literal ?: value
		var referencedTrust = rhs.trust ?: trust
		createCompoundTerm(
			"nodeCharacteristic",
			node.uniqueQuotedString,
			referencedCharacteristicType.uniqueQuotedString,
			referencedValue.uniqueQuotedString,
			referencedTrust.uniqueQuotedString
		)
	}
	
	protected def static Iterable<TrustedEnumCharacteristicType> findAllTrustedCharacteristicTypesInNodes(DataFlowDiagram dfd) {
		val characterizedNodes = dfd.eAllContents.filter(CharacterizedNode)
		characterizedNodes.flatMap[characteristics.iterator].filter(TrustedEnumCharacteristic).map[trustedEnumCharacteristicType].distinct as Iterable<TrustedEnumCharacteristicType>
	}
	
	protected def static Iterable<TrustedEnumCharacteristicType> findAllTrustedCharacteristicTypesInBehaviors(DataFlowDiagram dfd) {
		val characterizedNodes = dfd.eAllContents.filter(CharacterizedNode)
		val assignments = characterizedNodes.map[behavior].flatMap[assignments.iterator].toSet
		assignments.map[lhs].map[characteristicType].filter(TrustedEnumCharacteristicType).distinct as Iterable<TrustedEnumCharacteristicType>
	}
	
	def getLiteralForMembershipFunction(MembershipFunction funct, TrustedEnumCharacteristicType ct) {
		ct.trust.literals.findFirst[l| l.name == funct.name]
	}
	
}