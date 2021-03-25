package org.palladiosimulator.dataflow.uncertainty.fis.adapter

import java.util.List
import java.nio.file.Path

interface FuzzySystemExecution {
	
	def double runFIS(List<Double> inputs, Path fisPath)
}