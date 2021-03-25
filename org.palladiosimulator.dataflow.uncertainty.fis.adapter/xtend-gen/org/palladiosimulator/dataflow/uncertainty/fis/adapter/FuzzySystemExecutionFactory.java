package org.palladiosimulator.dataflow.uncertainty.fis.adapter;

import org.palladiosimulator.dataflow.uncertainty.fis.adapter.impl.FuzzyLiteAdapter;

@SuppressWarnings("all")
public class FuzzySystemExecutionFactory {
  public static FuzzySystemExecution create() {
    return new FuzzyLiteAdapter();
  }
}
