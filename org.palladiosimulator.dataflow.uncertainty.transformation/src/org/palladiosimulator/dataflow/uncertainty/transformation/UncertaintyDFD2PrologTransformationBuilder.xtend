package org.palladiosimulator.dataflow.uncertainty.transformation

import org.palladiosimulator.dataflow.uncertainty.transformation.impl.UncertaintyDFD2PrologTransformationImpl
import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.DFD2PrologTransformation
import org.palladiosimulator.dataflow.confidentiality.transformation.prolog.DFD2PrologTransformationBuilder

class UncertaintyDFD2PrologTransformationBuilder extends DFD2PrologTransformationBuilder {

	private new () {}

    override DFD2PrologTransformation build() {
        return new UncertaintyDFD2PrologTransformationImpl(nameProvider);
    }
    
    static def UncertaintyDFD2PrologTransformationBuilder create() {
        return new UncertaintyDFD2PrologTransformationBuilder();
    }
}