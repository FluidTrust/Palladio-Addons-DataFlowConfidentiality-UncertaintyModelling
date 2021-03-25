package org.palladiosimulator.dataflow.uncertainty.fis.transformation;

import com.google.common.base.Objects;
import java.io.File;
import java.io.FileOutputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import org.eclipse.emf.common.util.EList;
import org.eclipse.xtend2.lib.StringConcatenation;
import org.eclipse.xtext.xbase.lib.Exceptions;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.ACCU_Method;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.ACT_Operator;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.AND_Operator;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.DEFUZZY_Method;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.DefuzzificationFunction;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.FuzzificationFunction;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.FuzzyFunction;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.FuzzyInferenceSystem;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.GaussianMF;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.GeneralizedBellMF;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.MembershipFunction;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.OR_Operator;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.Rule;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.SMF;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.TrapezoidalMF;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.TriangularMF;
import org.palladiosimulator.dataflow.Uncertainty.FuzzyInferenceSystem.ZMF;

@SuppressWarnings("all")
public class FisFileGenerator {
  public Path doGenerate(final FuzzyInferenceSystem fis) {
    try {
      CharSequence output = this.compile(fis);
      Path tmpFisPath = Files.createTempFile(fis.getName(), ".fis");
      File tmpFis = tmpFisPath.toFile();
      tmpFis.deleteOnExit();
      String _string = tmpFisPath.toString();
      FileOutputStream fos = new FileOutputStream(_string);
      fos.write(output.toString().getBytes());
      fos.close();
      return tmpFisPath;
    } catch (Throwable _e) {
      throw Exceptions.sneakyThrow(_e);
    }
  }
  
  public CharSequence compile(final FuzzyInferenceSystem sys) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("[System]");
    _builder.newLine();
    _builder.append("Name=\'");
    String _name = sys.getName();
    _builder.append(_name);
    _builder.append("\'");
    _builder.newLineIfNotEmpty();
    _builder.append("Type=\'mamdani\'");
    _builder.newLine();
    _builder.append("Version=2.0");
    _builder.newLine();
    _builder.append("NumInputs=");
    int _size = sys.getInput().size();
    _builder.append(_size);
    _builder.newLineIfNotEmpty();
    _builder.append("NumOutputs=");
    int _size_1 = sys.getOutput().size();
    _builder.append(_size_1);
    _builder.newLineIfNotEmpty();
    _builder.append("NumRules=");
    int _size_2 = sys.getRules().size();
    _builder.append(_size_2);
    _builder.newLineIfNotEmpty();
    _builder.append("AndMethod=");
    CharSequence _compile = this.compile(sys.getAND());
    _builder.append(_compile);
    _builder.newLineIfNotEmpty();
    _builder.append("OrMethod=");
    CharSequence _compile_1 = this.compile(sys.getOR());
    _builder.append(_compile_1);
    _builder.newLineIfNotEmpty();
    _builder.append("ImpMethod=");
    CharSequence _compile_2 = this.compile(sys.getACT());
    _builder.append(_compile_2);
    _builder.newLineIfNotEmpty();
    _builder.append("AggMethod=");
    CharSequence _compile_3 = this.compile(sys.getACCU());
    _builder.append(_compile_3);
    _builder.newLineIfNotEmpty();
    _builder.append("DefuzzMethod=");
    CharSequence _compile_4 = this.compile(sys.getMETHOD());
    _builder.append(_compile_4);
    _builder.newLineIfNotEmpty();
    _builder.newLine();
    {
      EList<FuzzificationFunction> _input = sys.getInput();
      boolean _hasElements = false;
      for(final FuzzificationFunction in : _input) {
        if (!_hasElements) {
          _hasElements = true;
        } else {
          _builder.appendImmediate("\n", "");
        }
        _builder.append("[Input");
        int _indexOf = sys.getInput().indexOf(in);
        int _plus = (_indexOf + 1);
        _builder.append(_plus);
        _builder.append("]");
        _builder.newLineIfNotEmpty();
        CharSequence _compile_5 = this.compile(in);
        _builder.append(_compile_5);
        _builder.newLineIfNotEmpty();
      }
    }
    _builder.newLine();
    {
      EList<DefuzzificationFunction> _output = sys.getOutput();
      for(final DefuzzificationFunction out : _output) {
        _builder.append("[Output");
        int _indexOf_1 = sys.getOutput().indexOf(out);
        int _plus_1 = (_indexOf_1 + 1);
        _builder.append(_plus_1);
        _builder.append("]");
        _builder.newLineIfNotEmpty();
        CharSequence _compile_6 = this.compile(out);
        _builder.append(_compile_6);
        _builder.newLineIfNotEmpty();
      }
    }
    _builder.newLine();
    _builder.append("[Rules]");
    _builder.newLine();
    {
      EList<Rule> _rules = sys.getRules();
      for(final Rule rule : _rules) {
        {
          EList<FuzzificationFunction> _input_1 = sys.getInput();
          boolean _hasElements_1 = false;
          for(final FuzzificationFunction sysIn : _input_1) {
            if (!_hasElements_1) {
              _hasElements_1 = true;
            } else {
              _builder.appendImmediate(" ", "");
            }
            int _ruleMFIndex = this.getRuleMFIndex(sysIn, rule.getInputs());
            _builder.append(_ruleMFIndex);
          }
        }
        _builder.append(", ");
        {
          EList<DefuzzificationFunction> _output_1 = sys.getOutput();
          boolean _hasElements_2 = false;
          for(final DefuzzificationFunction sysOut : _output_1) {
            if (!_hasElements_2) {
              _hasElements_2 = true;
            } else {
              _builder.appendImmediate(" ", "");
            }
            int _ruleMFIndex_1 = this.getRuleMFIndex(sysOut, rule.getOutput());
            _builder.append(_ruleMFIndex_1);
          }
        }
        _builder.append(" (1) : ");
        int _value = rule.getOperator().getValue();
        _builder.append(_value);
        _builder.newLineIfNotEmpty();
      }
    }
    return _builder;
  }
  
  public int getRuleMFIndex(final FuzzyFunction funct, final EList<MembershipFunction> ruleMFS) {
    for (final MembershipFunction ruleFunct : ruleMFS) {
      FuzzyFunction _parentFuzzyFunction = ruleFunct.getParentFuzzyFunction();
      boolean _equals = Objects.equal(_parentFuzzyFunction, funct);
      if (_equals) {
        int _indexOf = funct.getTerm().indexOf(ruleFunct);
        return (_indexOf + 1);
      }
    }
    return 0;
  }
  
  public CharSequence compile(final FuzzyFunction funct) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("Name=\'");
    String _name = funct.getName();
    _builder.append(_name);
    _builder.append("\'");
    _builder.newLineIfNotEmpty();
    _builder.append("Range=[");
    Double _get = funct.getRange().get(0);
    _builder.append(_get);
    _builder.append(" ");
    Double _get_1 = funct.getRange().get(1);
    _builder.append(_get_1);
    _builder.append("]");
    _builder.newLineIfNotEmpty();
    _builder.append("NumMFs=");
    int _size = funct.getTerm().size();
    _builder.append(_size);
    _builder.newLineIfNotEmpty();
    {
      EList<MembershipFunction> _term = funct.getTerm();
      for(final MembershipFunction mf : _term) {
        _builder.append("MF");
        int _indexOf = funct.getTerm().indexOf(mf);
        int _plus = (_indexOf + 1);
        _builder.append(_plus);
        _builder.append("=");
        CharSequence _compile = this.compile(mf);
        _builder.append(_compile);
        _builder.newLineIfNotEmpty();
      }
    }
    return _builder;
  }
  
  public CharSequence compile(final MembershipFunction mf) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("\'");
    String _name = mf.getName();
    _builder.append(_name);
    _builder.append("\':");
    {
      if ((mf instanceof TriangularMF)) {
        CharSequence _compile = this.compile(((TriangularMF)mf));
        _builder.append(_compile);
        _builder.newLineIfNotEmpty();
      } else {
        if ((mf instanceof GaussianMF)) {
          CharSequence _compile_1 = this.compile(((GaussianMF)mf));
          _builder.append(_compile_1);
          _builder.newLineIfNotEmpty();
        } else {
          if ((mf instanceof TrapezoidalMF)) {
            CharSequence _compile_2 = this.compile(((TrapezoidalMF)mf));
            _builder.append(_compile_2);
            _builder.newLineIfNotEmpty();
          } else {
            if ((mf instanceof GeneralizedBellMF)) {
              CharSequence _compile_3 = this.compile(((GeneralizedBellMF)mf));
              _builder.append(_compile_3);
              _builder.newLineIfNotEmpty();
            } else {
              if ((mf instanceof SMF)) {
                CharSequence _compile_4 = this.compile(((SMF)mf));
                _builder.append(_compile_4);
                _builder.newLineIfNotEmpty();
              } else {
                if ((mf instanceof ZMF)) {
                  CharSequence _compile_5 = this.compile(((ZMF)mf));
                  _builder.append(_compile_5);
                  _builder.newLineIfNotEmpty();
                }
              }
            }
          }
        }
      }
    }
    return _builder;
  }
  
  public CharSequence compile(final TriangularMF mf) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("\'trimf\',[");
    double _a = mf.getA();
    _builder.append(_a);
    _builder.append(" ");
    double _b = mf.getB();
    _builder.append(_b);
    _builder.append(" ");
    double _m = mf.getM();
    _builder.append(_m);
    _builder.append("]");
    return _builder;
  }
  
  public CharSequence compile(final GaussianMF mf) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("\'gaussmf\',[");
    double _o = mf.getO();
    _builder.append(_o);
    _builder.append(" ");
    double _m = mf.getM();
    _builder.append(_m);
    _builder.append("]");
    return _builder;
  }
  
  public CharSequence compile(final TrapezoidalMF mf) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("\'trapmf\',[");
    double _a = mf.getA();
    _builder.append(_a);
    _builder.append(" ");
    double _b = mf.getB();
    _builder.append(_b);
    _builder.append(" ");
    double _c = mf.getC();
    _builder.append(_c);
    _builder.append(" ");
    double _d = mf.getD();
    _builder.append(_d);
    _builder.append("]");
    return _builder;
  }
  
  public CharSequence compile(final GeneralizedBellMF mf) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("\'gbellmf\',[");
    double _a = mf.getA();
    _builder.append(_a);
    _builder.append(" ");
    double _b = mf.getB();
    _builder.append(_b);
    _builder.append(" ");
    double _c = mf.getC();
    _builder.append(_c);
    _builder.append("]");
    return _builder;
  }
  
  public CharSequence compile(final SMF mf) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("\'smf\',[");
    double _a = mf.getA();
    _builder.append(_a);
    _builder.append(" ");
    double _b = mf.getB();
    _builder.append(_b);
    _builder.append("]");
    return _builder;
  }
  
  public CharSequence compile(final ZMF mf) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("\'zmf\',[");
    double _a = mf.getA();
    _builder.append(_a);
    _builder.append(" ");
    double _b = mf.getB();
    _builder.append(_b);
    _builder.append("]");
    return _builder;
  }
  
  public CharSequence compile(final AND_Operator op) {
    StringConcatenation _builder = new StringConcatenation();
    {
      int _value = op.getValue();
      boolean _equals = (_value == 0);
      if (_equals) {
        _builder.append("\'min\'");
        _builder.newLineIfNotEmpty();
      } else {
        int _value_1 = op.getValue();
        boolean _equals_1 = (_value_1 == 1);
        if (_equals_1) {
          _builder.append("\'prod\'");
          _builder.newLineIfNotEmpty();
        } else {
          int _value_2 = op.getValue();
          boolean _equals_2 = (_value_2 == 2);
          if (_equals_2) {
            _builder.append("\'bounded_difference\'");
            _builder.newLineIfNotEmpty();
          }
        }
      }
    }
    return _builder;
  }
  
  public CharSequence compile(final OR_Operator op) {
    StringConcatenation _builder = new StringConcatenation();
    {
      int _value = op.getValue();
      boolean _equals = (_value == 0);
      if (_equals) {
        _builder.append("\'max\'");
        _builder.newLineIfNotEmpty();
      } else {
        int _value_1 = op.getValue();
        boolean _equals_1 = (_value_1 == 1);
        if (_equals_1) {
          _builder.append("\'probor\'");
          _builder.newLineIfNotEmpty();
        } else {
          int _value_2 = op.getValue();
          boolean _equals_2 = (_value_2 == 2);
          if (_equals_2) {
            _builder.append("\'bounded_sum\'");
            _builder.newLineIfNotEmpty();
          }
        }
      }
    }
    return _builder;
  }
  
  public CharSequence compile(final ACT_Operator op) {
    StringConcatenation _builder = new StringConcatenation();
    {
      int _value = op.getValue();
      boolean _equals = (_value == 0);
      if (_equals) {
        _builder.append("\'prod\'");
        _builder.newLineIfNotEmpty();
      } else {
        int _value_1 = op.getValue();
        boolean _equals_1 = (_value_1 == 1);
        if (_equals_1) {
          _builder.append("\'min\'");
          _builder.newLineIfNotEmpty();
        }
      }
    }
    return _builder;
  }
  
  public CharSequence compile(final ACCU_Method op) {
    StringConcatenation _builder = new StringConcatenation();
    {
      int _value = op.getValue();
      boolean _equals = (_value == 0);
      if (_equals) {
        _builder.append("\'max\'");
        _builder.newLineIfNotEmpty();
      } else {
        int _value_1 = op.getValue();
        boolean _equals_1 = (_value_1 == 1);
        if (_equals_1) {
          _builder.append("\'bounded_sum\'");
          _builder.newLineIfNotEmpty();
        } else {
          int _value_2 = op.getValue();
          boolean _equals_2 = (_value_2 == 2);
          if (_equals_2) {
            _builder.append("\'normalized_sum\'");
            _builder.newLineIfNotEmpty();
          }
        }
      }
    }
    return _builder;
  }
  
  public CharSequence compile(final DEFUZZY_Method op) {
    StringConcatenation _builder = new StringConcatenation();
    {
      int _value = op.getValue();
      boolean _equals = (_value == 0);
      if (_equals) {
        _builder.append("\'centroid\'");
        _builder.newLineIfNotEmpty();
      } else {
        int _value_1 = op.getValue();
        boolean _equals_1 = (_value_1 == 1);
        if (_equals_1) {
          _builder.append("\'bisector\'");
          _builder.newLineIfNotEmpty();
        } else {
          int _value_2 = op.getValue();
          boolean _equals_2 = (_value_2 == 2);
          if (_equals_2) {
            _builder.append("\'som\'");
            _builder.newLineIfNotEmpty();
          } else {
            int _value_3 = op.getValue();
            boolean _equals_3 = (_value_3 == 3);
            if (_equals_3) {
              _builder.append("\'lom\'");
              _builder.newLineIfNotEmpty();
            }
          }
        }
      }
    }
    return _builder;
  }
}
