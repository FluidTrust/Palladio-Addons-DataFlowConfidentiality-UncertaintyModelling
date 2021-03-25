package org.palladiosimulator.dataflow.uncertainty.fis.adapter

import java.util.List

interface FuzzySystemExecution {
	
	def double runFIS(List<Double> inputs, String fisPath)
}