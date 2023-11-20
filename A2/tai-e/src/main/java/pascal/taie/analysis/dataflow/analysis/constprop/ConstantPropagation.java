/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
    AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact fact = new CPFact();

        // init the params to NAC for safety
        cfg.getIR().getParams().forEach(p -> {
            if (p.getType() instanceof PrimitiveType) {
                fact.update(p, Value.getNAC());
            }
        });
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((var, val) -> {
            Value targetVal = target.get(var);
            target.update(var, meetValue(val, targetVal));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        Value ret = Value.getNAC();
        if (v1.isNAC() || v2.isNAC()) {
            ret = Value.getNAC();
        } else if (v1.isUndef() || v2.isUndef()) {
            ret = v1.isUndef() ? v2 : v1;
        } else if (v1.isConstant() && v2.isConstant() && v1.getConstant() == v2.getConstant()) {
            return v1;
        }

        return ret;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact outCopy = out.copy();
        out.copyFrom(in);

        stmt.getDef().ifPresent(def -> {
            stmt.getUses().forEach(use -> {
                // only processing Var, IntLiteral and BinaryExp, NAC for other case
                out.update((Var) def, evaluate(use, in));
            });
        });

        return !out.equals(outCopy);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        Value value = Value.getNAC();

        if (exp instanceof Var) {
            // get value from in fact
            value = in.get((Var) exp);
        } else if (exp instanceof IntLiteral) {
            value = Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof BinaryExp) {
            Var left = ((BinaryExp) exp).getOperand1();
            Var right = ((BinaryExp) exp).getOperand2();
            if (canHoldInt(left) && canHoldInt(right) && in.get(left).isConstant() && in.get(right).isConstant()) {
                int leftVal = in.get(left).getConstant();
                int rightVal = in.get(right).getConstant();
                if (exp instanceof ArithmeticExp) {
                    value = artifactEvaluate(exp, leftVal, rightVal);
                } else if (exp instanceof BitwiseExp) {
                    value = bitwiseEvaluate(exp, leftVal, rightVal);
                } else if (exp instanceof ConditionExp) {
                    value = conditionEvaluate(exp, leftVal, rightVal);
                } else if (exp instanceof ShiftExp) {
                    value = shiftEvaluate(exp, leftVal, rightVal);
                }
            }
        }

        return value;
    }

    public static Value artifactEvaluate(Exp exp, int left, int right) {
        Value value = Value.getNAC();

        if (exp instanceof ArithmeticExp) {
            ArithmeticExp.Op ops = ((ArithmeticExp) exp).getOperator();
            switch (ops) {
                case ADD:
                    value = Value.makeConstant(left + right);
                    break;
                case SUB:
                    value = Value.makeConstant(left - right);
                    break;
                case MUL:
                    value = Value.makeConstant(left * right);
                    break;
                case DIV:
                    // div 0
                    if (right == 0) {
                        value = Value.getUndef();
                    } else {
                        value = Value.makeConstant(left / right);
                    }
                    break;
            }
        }

        return value;
    }

    public static Value bitwiseEvaluate(Exp exp, int left, int right) {
        Value value = Value.getNAC();

        if (exp instanceof BitwiseExp) {
            BitwiseExp.Op ops = ((BitwiseExp) exp).getOperator();
            switch (ops) {
                case OR:
                    value = Value.makeConstant(left | right);
                    break;
                case AND:
                    value = Value.makeConstant(left & right);
                    break;
                case XOR:
                    value = Value.makeConstant(left ^ right);
                    break;
            }
        }

        return value;
    }

    public static Value conditionEvaluate(Exp exp, int left, int right) {
        Value value = Value.getNAC();

        if (exp instanceof ConditionExp) {
            ConditionExp.Op ops = ((ConditionExp) exp).getOperator();
            switch (ops) {
                case EQ:
                    value = Value.makeConstant(left == right ? 1 : 0);
                    break;
                case NE:
                    value = Value.makeConstant(left != right ? 1 : 0);
                    break;
                case LT:
                    value = Value.makeConstant(left < right ? 1 : 0);
                    break;
                case LE:
                    value = Value.makeConstant(left <= right ? 1 : 0);
                    break;
                case GT:
                    value = Value.makeConstant(left > right ? 1 : 0);
                    break;
                case GE:
                    value = Value.makeConstant(left >= right ? 1 : 0);
                    break;
            }
        }

        return value;
    }

    public static Value shiftEvaluate(Exp exp, int left, int right) {
        Value value = Value.getNAC();

        if (exp instanceof ShiftExp) {
            ShiftExp.Op ops = ((ShiftExp) exp).getOperator();
            switch (ops) {
                case SHL:
                    value = Value.makeConstant(left << right);
                    break;
                case SHR:
                    value = Value.makeConstant(left >> right);
                    break;
                case USHR:
                    value = Value.makeConstant(left >>> right);
                    break;
            }
        }

        return value;
    }
}
