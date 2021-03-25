package org.palladiosimulator.dataflow.uncertainty.fis.adapter

import org.palladiosimulator.dataflow.uncertainty.fis.adapter.impl.FuzzyLiteAdapter
import java.util.List

class AdapterTest {
	def static void main(String[] args) {
		var adapter = new FuzzyLiteAdapter
		println(adapter.runFIS(List.of(50.0, 1.0),"/home/nicolas/Dokumente/Uni/Masterarbeit/GPSFIS.fis"))
		
	}
}