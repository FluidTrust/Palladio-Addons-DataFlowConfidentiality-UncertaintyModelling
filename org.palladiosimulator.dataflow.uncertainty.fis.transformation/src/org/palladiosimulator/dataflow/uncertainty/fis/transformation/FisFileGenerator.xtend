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
import java.io.FileOutputStream
import java.nio.file.Files
import java.io.IOException
import java.nio.file.Path

class FisFileGenerator { 
	
	static def doGenerate(FuzzyInferenceSystem fis) {
		var output = fis.compile
		var FileOutputStream fos
		var Path tmpFisPath
		try {
			tmpFisPath = Files.createTempFile(fis.name, ".fis")
			var tmpFis = tmpFisPath.toFile
		    tmpFis.deleteOnExit
			fos = new FileOutputStream(tmpFisPath.toString);
			fos.write(output.toString.bytes)
		} catch(IOException e) {
			e.printStackTrace
		} finally {
			fos.close
		}
		
		return tmpFisPath
	}
	
	static def compile(FuzzyInferenceSystem sys) '''
	[System]
	Name='«sys.name»'
	Type='mamdani'
	Version=2.0
	NumInputs=«sys.input.size»
	NumOutputs=1
	NumRules=«sys.rules.size»
	AndMethod=«sys.AND.compile»
	OrMethod=«sys.OR.compile»
	ImpMethod=«sys.ACT.compile»
	AggMethod=«sys.ACCU.compile»
	DefuzzMethod=«sys.METHOD.compile»
	
	«FOR in:sys.input SEPARATOR "\n" »
	[Input«sys.input.indexOf(in)+1»]
	«in.compile»
	«ENDFOR»
	
	
	[Output 1]
	«sys.output.compile»
	
	[Rules]
	«FOR rule:sys.rules»
	«FOR sysIn:sys.input SEPARATOR ' '»«getRuleMFIndex(sysIn, rule.inputs)»«ENDFOR», «getRuleMFIndex(sys.output, rule.output)» (1) : «rule.operator.value»
	«ENDFOR»
	'''
	
	static def getRuleMFIndex(FuzzyFunction funct, EList<MembershipFunction> ruleMFS) {
		for(ruleFunct:ruleMFS) {
			if(ruleFunct.parentFuzzyFunction == funct) {
				return funct.term.indexOf(ruleFunct)+1 // uses the conventional counting, starting at 1
			}
		}
		// the index 0 implies, that no mf of this input is used
		return 0
	}
	
	static def compile(FuzzyFunction funct)'''
	Name='«funct.name»'
	Range=[«funct.range.get(0)» «funct.range.get(1)»]
	NumMFs=«funct.term.size»
	«FOR mf:funct.term»
	MF«funct.term.indexOf(mf)+1»=«mf.compile»
	«ENDFOR»
	'''
	
	static def compile(MembershipFunction mf) '''
	'«mf.name»':«mf.compileMF»
	'''
	
	static def dispatch compileMF(TriangularMF mf) ''''trimf',[«mf.a» «mf.m» «mf.b»]'''
	
	static def dispatch compileMF(GaussianMF mf) ''''gaussmf',[«mf.o» «mf.m»]'''
	
	static def dispatch compileMF(TrapezoidalMF mf) ''''trapmf',[«mf.a» «mf.b» «mf.c» «mf.d»]'''
	
	static def dispatch compileMF(GeneralizedBellMF mf) ''''gbellmf',[«mf.a» «mf.b» «mf.c»]'''
	
	static def dispatch compileMF(SMF mf) ''''smf',[«mf.a» «mf.b»]'''
	
	static def dispatch compileMF(ZMF mf) ''''zmf',[«mf.a» «mf.b»]'''
	
	static def compile(AND_Operator op) '''
	«IF op.value == 0»'min'
	«ELSEIF op.value == 1»'prod'
	«ELSEIF op.value == 2»'bounded_difference'
	«ENDIF»'''
	
	static def compile(OR_Operator op) '''
	«IF op.value == 0»'max'
	«ELSEIF op.value == 1»'probor'
	«ELSEIF op.value == 2»'bounded_sum'
	«ENDIF»'''
	
	static def compile(ACT_Operator op) '''
	«IF op.value == 0»'prod'
	«ELSEIF op.value == 1»'min'
	«ENDIF»'''
	
	static def compile(ACCU_Method op) '''
	«IF op.value == 0»'max'
	«ELSEIF op.value == 1»'bounded_sum'
	«ELSEIF op.value == 2»'normalized_sum'
	«ENDIF»'''
	
	static def compile(DEFUZZY_Method op) '''
	«IF op.value == 0»'centroid'
	«ELSEIF op.value == 1»'bisector'
	«ELSEIF op.value == 2»'som'
	«ELSEIF op.value == 3»'lom'
	«ENDIF»'''
}