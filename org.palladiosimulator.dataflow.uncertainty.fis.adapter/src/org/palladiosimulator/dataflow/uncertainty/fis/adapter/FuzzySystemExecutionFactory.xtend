package org.palladiosimulator.dataflow.uncertainty.fis.adapter

import org.palladiosimulator.dataflow.uncertainty.fis.adapter.impl.FuzzyLiteAdapter

class FuzzySystemExecutionFactory {
	static def FuzzySystemExecution create() {
		return new FuzzyLiteAdapter;
	}
}