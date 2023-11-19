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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
            ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
            ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        // data-flow dead code
        Set<Stmt> unreachable = new HashSet<>(cfg.getNodes());

        Stack<Stmt> worklist = new Stack<>();
        Stmt entry = cfg.getEntry();
        worklist.add(entry);
        unreachable.remove(entry);

        while (!worklist.isEmpty()) {
            Stmt stmt = worklist.pop();
            cfg.getOutEdgesOf(stmt).forEach(e -> {
                worklist.add(e.getTarget());
                unreachable.remove(e.getTarget());
            });

            if (stmt instanceof If) {
                ConditionExp exp = ((If) stmt).getCondition();
                Value val = ConstantPropagation.evaluate(exp, constants.getInFact(stmt));
                if (val.isConstant()) {
                    cfg.getOutEdgesOf(stmt).forEach(e -> {
                        if ((e.getKind() == Edge.Kind.IF_TRUE && val.getConstant() <= 0) || (e.getKind() == Edge.Kind.IF_FALSE && val.getConstant() > 0)) {
                            // successor is dead code
                            worklist.remove(e.getTarget());
                            unreachable.add(e.getTarget());
                        }
                    });
                }
            } else if (stmt instanceof SwitchStmt) {
                Var var = ((SwitchStmt) stmt).getVar();
                Value val = ConstantPropagation.evaluate(var, constants.getInFact(stmt));
                if (val.isConstant()) {
                    AtomicBoolean defaultCase = new AtomicBoolean(true);
                    AtomicInteger caseVal = new AtomicInteger();
                    ((SwitchStmt) stmt).getCaseTargets().forEach(t -> {
                        if (val.getConstant() == t.first()) {
                            defaultCase.set(false);
                            caseVal.set(t.first());
                        }
                    });

                    if (defaultCase.get()) {
                        // all cases are unreachable
                        ((SwitchStmt) stmt).getCaseTargets().forEach(t -> {
                            worklist.remove(t.second());
                            unreachable.add(t.second());
                        });
                     } else {
                        // only the default case and other cases is unreachable
                        ((SwitchStmt) stmt).getCaseTargets().forEach(t -> {
                            if (t.first() != caseVal.get()) {
                                worklist.remove(t.second());
                                unreachable.add(t.second());
                            }
                        });
                        Stmt defaultStmt = ((SwitchStmt) stmt).getDefaultTarget();
                        worklist.remove(defaultStmt);
                        unreachable.add(defaultStmt);
                    }
                }
            }
        }

        // control flow unreachable node
        unreachable.forEach(n -> {
            deadCode.add(n);
        });

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
            // cast may trigger ClassCastException
            rvalue instanceof CastExp ||
            // static field access may trigger class initialization
            // instance field access may trigger NPE
            rvalue instanceof FieldAccess ||
            // array access may trigger NPE
            rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
