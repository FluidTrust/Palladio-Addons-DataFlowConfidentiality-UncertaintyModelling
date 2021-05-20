package org.palladiosimulator.dataflow.uncertainty.transformation.impl

import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.impl.DFD2PrologTransformationParameter
import org.palladiosimulator.dataflow.diagram.characterized.DataFlowDiagramCharacterized.CharacterizedNode
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.Literal
import org.eclipse.xtend.lib.annotations.Accessors
import org.palladiosimulator.dataflow.dictionary.characterized.DataDictionaryCharacterized.Pin
import org.palladiosimulator.dataflow.Uncertainty.TrustedEnumCharacteristicType

class UncertaintyDFD2PrologTransformationParameter extends DFD2PrologTransformationParameter {
	
	@Accessors var Literal t
	@Accessors var TrustedEnumCharacteristicType trustedCt
	
	new(CharacterizedNode node, TrustedEnumCharacteristicType ct, Literal l, Literal t) {
		super(node, ct, l)
		this.trustedCt = ct
		this.t = t
	}
	
	new(CharacterizedNode node, Pin pin, TrustedEnumCharacteristicType ct, Literal l, Literal t) {
		super(node, pin, ct, l)
		this.trustedCt = ct
		this.t = t
	}
	
}