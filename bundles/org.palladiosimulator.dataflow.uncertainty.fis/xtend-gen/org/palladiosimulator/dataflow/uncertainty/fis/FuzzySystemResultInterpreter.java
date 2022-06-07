package org.palladiosimulator.dataflow.uncertainty.fis;

import java.util.List;
import org.eclipse.xtext.xbase.lib.Functions.Function1;
import org.eclipse.xtext.xbase.lib.ListExtensions;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.MembershipFunction;

@SuppressWarnings("all")
public class FuzzySystemResultInterpreter {
  private FuzzySystemResultInterpreter() {
  }
  
  /**
   * Transforms the result
   */
  public static MembershipFunction getMaxMembershipFunction(final List<MembershipFunction> terms, final double executionResult) {
    final Function1<MembershipFunction, Double> _function = (MembershipFunction t) -> {
      return Double.valueOf(t.calculateTrustWeight(executionResult));
    };
    List<Double> membershipValues = ListExtensions.<MembershipFunction, Double>map(terms, _function);
    int membership = 0;
    double maxMembershipValue = Double.MIN_VALUE;
    for (int i = 0; (i < membershipValues.size()); i++) {
      Double _get = membershipValues.get(i);
      boolean _greaterThan = ((_get).doubleValue() > maxMembershipValue);
      if (_greaterThan) {
        membership = i;
        maxMembershipValue = (membershipValues.get(i)).doubleValue();
      }
    }
    return terms.get(membership);
  }
}
