package org.palladiosimulator.dataflow.uncertainty.transformation.workflow.tests.scalability

import java.util.HashMap
import java.util.List
import java.util.Map
import java.util.ArrayList
import java.util.Collections

class ScalabilityTestTimeMapper {
	
	var Map<Integer, List<Long> > timeMap
	
	private var String name
	private var int start
	private var int end
	private var int factor
	
	new(String name, int testStart, int testMaxIteration, int iterationFactor) {
		this.name = name
		this.start = testStart
		this.end = testMaxIteration
		this.factor = iterationFactor
		
		timeMap = new HashMap<Integer, List<Long> >
		timeMap.initializeTimeMap
	}
	
	def addTime(int iteration, long time) {
		timeMap.get(iteration).add(time)
	}
	
	def void initializeTimeMap(Map<Integer, List<Long> > map) {
		for(var i = start; i <= end; i= i*factor) {
			map.put(i, new ArrayList<Long>)
		}
	}
	
	def void calculateAndPrintMeanTimes() {
		var meanTimes = new ArrayList<Long>
		for(var i = start; i <= end; i= i*factor) {
			var meanTime = calculateMean(timeMap.get(i))
			
			meanTimes.add(meanTime)
		}
		
		println("Mean " + name + ": " + meanTimes.toString)
	}
	
	def void calculateAndPrintMedianTimes() {
		var medianTimes = new ArrayList<Long>
		for(var i = start; i <= end; i= i*factor) {
			var medianTime = calculateMedian(timeMap.get(i))
			
			medianTimes.add(medianTime)
		}
		
		println("Median " + name + ": " + medianTimes.toString)
	}
	
	static def calculateMean(List<Long> list) {
		var long sum = 0
		for(long tmp : list) {
			sum += tmp
		}
		(sum/list.size)
	}
	
	static def calculateMedian(List<Long> list) {
		Collections.sort(list)
		var long median
		if (list.size % 2 == 0) {
			median = (list.get(list.size/2) + list.get(list.size/2 - 1))/2
		} else {
			median = list.get(list.size/2)
		}
		median
	}
	
}