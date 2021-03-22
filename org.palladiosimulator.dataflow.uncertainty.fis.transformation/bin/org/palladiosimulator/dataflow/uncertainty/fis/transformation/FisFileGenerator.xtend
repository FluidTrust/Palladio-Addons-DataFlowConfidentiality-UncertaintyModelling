package org.palladiosimulator.dataflow.uncertainty.fis.transformation

import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.FuzzyInferenceSystem
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.AND_Operator
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.OR_Operator
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.ACT_Operator
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.ACCU_Method
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.DEFUZZY_Method
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.FuzzyFunction
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.TriangularMF
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.GaussianMF
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.TrapezoidalMF
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.GeneralizedBellMF
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.SMF
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.ZMF
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.MembershipFunction
import org.eclipse.emf.common.util.EList
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.FISContainer

class FisFileGenerator {
	
	def doGenerate(FISContainer container) {
		for(fis:container.fuzzyInferenceSystems) {
			fis.compile
		}
	}
	
	def compile(FuzzyInferenceSystem sys) '''
	[System]
	Name = '«sys.name»'
	Type = 'mamdani'
	Version = 2.0
	NumInputs=«sys.input.size»
	NumOutputs=«sys.output.size»
	NumRules=«sys.rules.size»
	AndMethod=«sys.AND.compile»
	OrMethod=«sys.OR.compile»
	ImpMethod=«sys.ACT.compile»
	AggMethod=«sys.ACCU.compile»
	DefuzzMethod=«sys.METHOD.compile»
	
	«FOR in:sys.input»
	[Input«sys.input.indexOf(in)+1»]
	«in.compile»
	«ENDFOR»
	
	«FOR out:sys.output»
	[Output«sys.output.indexOf(out)+1»]
	«out.compile»
	«ENDFOR»
	
	[Rules]
	«FOR rule:sys.rules»
	«FOR sysIn:sys.input SEPARATOR ' '»
	«getRuleMFIndex(sysIn, rule.inputs)»
	«ENDFOR»
	,
	«FOR sysOut:sys.output SEPARATOR ' '»
	«getRuleMFIndex(sysOut, rule.output)»
	«ENDFOR»
	 (1) : «rule.operator.value»
	«ENDFOR»
	'''
	
	def getRuleMFIndex(FuzzyFunction funct, EList<MembershipFunction> ruleMFS) {
		for(ruleFunct:ruleMFS) {
			if(ruleFunct.parentFuzzyFunction == funct) {
				return funct.term.indexOf(ruleFunct)+1
			}
		}
		return 0
	}
	
	def compile(FuzzyFunction funct)'''
	Name='«funct.name»'
	Range=[«funct.range.get(0)» «funct.range.get(1)»]
	NumMFs=«funct.term.size»
	«FOR mf:funct.term»
	MF«funct.term.indexOf(mf)+1»=«mf.compile»
	«ENDFOR»
	'''
	
	def compile(MembershipFunction mf) '''
	'«mf.name»':
	«IF mf instanceof TriangularMF»«mf.compile»
	«ELSEIF mf instanceof GaussianMF»«mf.compile»
	«ELSEIF mf instanceof TrapezoidalMF»«mf.compile»
	«ELSEIF mf instanceof GeneralizedBellMF»«mf.compile»
	«ELSEIF mf instanceof SMF»«mf.compile»
	«ELSEIF mf instanceof ZMF»«mf.compile»
	«ENDIF»
	'''
	
	def compile(TriangularMF mf) '''
	'trimf',[«mf.a» «mf.b» «mf.c»]
	'''
	
	def compile(GaussianMF mf) '''
	'gaussmf',[«mf.o» «mf.c»]
	'''
	
	def compile(TrapezoidalMF mf) '''
	'trapmf',[«mf.a» «mf.b» «mf.c» «mf.d»]
	'''
	
	def compile(GeneralizedBellMF mf) '''
	'gbellmf',[«mf.a» «mf.b» «mf.c»]
	'''
	
	def compile(SMF mf) '''
	'smf',[«mf.a» «mf.c»]
	'''
	
	def compile(ZMF mf) '''
	'zmf',[«mf.a» «mf.c»]
	'''
	
	def compile(AND_Operator op) '''
	«IF op.value == 0»'min'
	«ELSEIF op.value == 1»'prod'
	«ELSEIF op.value == 2»'bounded_difference'
	«ENDIF»'''
	
	def compile(OR_Operator op) '''
	«IF op.value == 0»'max'
	«ELSEIF op.value == 1»'probor'
	«ELSEIF op.value == 2»'bounded_sum'
	«ENDIF»'''
	
	def compile(ACT_Operator op) '''
	«IF op.value == 0»'prod'
	«ELSEIF op.value == 1»'min'
	«ENDIF»'''
	
	def compile(ACCU_Method op) '''
	«IF op.value == 0»'max'
	«ELSEIF op.value == 1»'bounded_sum'
	«ELSEIF op.value == 2»'normalized_sum'
	«ENDIF»'''
	
	def compile(DEFUZZY_Method op) '''
	«IF op.value == 0»'centroid'
	«ELSEIF op.value == 1»'bisector'
	«ELSEIF op.value == 2»'som'
	«ELSEIF op.value == 3»'lom'
	«ENDIF»'''
}