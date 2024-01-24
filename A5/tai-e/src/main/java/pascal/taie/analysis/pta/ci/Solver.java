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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.Type;

import java.util.Set;
import java.util.stream.Collectors;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (this.callGraph.contains(method)) {
            return;
        }

        this.callGraph.addReachableMethod(method);
        method.getIR().getStmts().forEach(stmt -> {
            if (stmt instanceof New || stmt instanceof Copy) {
                stmt.accept(this.stmtProcessor);
            }
        });
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private Obj obj;

        public void setObj(Obj obj) {
            this.obj = obj;
        }

        @Override
        public Void visit(New stmt) {
            Var l = stmt.getLValue();
            Obj obj = heapModel.getObj(stmt);
            //if (l.getType() instanceof ArrayType) {
            //    workList.addEntry(pointerFlowGraph.getArrayIndex(obj), new PointsToSet(obj));
            //} else {
            workList.addEntry(pointerFlowGraph.getVarPtr(l), new PointsToSet(obj));
            //}

            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            // Assign
            addPFGEdge(
                pointerFlowGraph.getVarPtr(stmt.getRValue()),
                pointerFlowGraph.getVarPtr(stmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {
            addPFGEdge(
                pointerFlowGraph.getArrayIndex(this.obj),
                pointerFlowGraph.getVarPtr(stmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(StoreArray stmt) {
            addPFGEdge(
                pointerFlowGraph.getVarPtr(stmt.getRValue()),
                pointerFlowGraph.getArrayIndex(this.obj)
            );
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            // should consider static field
            if (stmt.getFieldRef().isStatic()) {
                // y = T.f
                addPFGEdge(
                    pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue())
                );
            } else {
                // y = x.f
                addPFGEdge(
                    pointerFlowGraph.getInstanceField(this.obj, stmt.getFieldRef().resolve()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue())
                );
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            // should consider static field
            if (stmt.getFieldRef().isStatic()) {
                // T.f = y
                addPFGEdge(
                    pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()));
            } else {
                // x.f = y
                addPFGEdge(
                    pointerFlowGraph.getInstanceField(this.obj, stmt.getFieldRef().resolve()),
                    pointerFlowGraph.getVarPtr(stmt.getRValue()));
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     * AddEdge(source, target)
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        Set<Pointer> succs = this.pointerFlowGraph.getSuccsOf(source).stream().filter(sc -> sc.equals(target)).collect(Collectors.toSet());
        if (succs.isEmpty()) {
            this.pointerFlowGraph.addEdge(source, target);
            PointsToSet pointsToSet = source.getPointsToSet();
            if (!pointsToSet.isEmpty()) {
                this.workList.addEntry(target, pointsToSet);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!this.workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet diffs = this.propagate(entry.pointer(), entry.pointsToSet());

            if (entry.pointer() instanceof VarPtr p) {
                diffs.forEach(diffObj -> {
                    // processing store and load statement
                    Var var = p.getVar();
                    this.stmtProcessor.setObj(diffObj);
                    var.getStoreArrays().forEach(storeArray -> {
                        storeArray.accept(this.stmtProcessor);
                    });
                    var.getStoreFields().forEach(storeField -> {
                        storeField.accept(this.stmtProcessor);
                    });
                    var.getLoadArrays().forEach(loadArray -> {
                        loadArray.accept(this.stmtProcessor);
                    });
                    var.getLoadFields().forEach(loadField -> {
                        loadField.accept(this.stmtProcessor);
                    });
                    this.processCall(var, diffObj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // calculate the diff of pointsToSet
        PointsToSet diff = new PointsToSet();
        pointsToSet.forEach(p -> {
            if (!pointer.getPointsToSet().contains(p)) {
                diff.addObject(p);
            }
        });

        if (!pointsToSet.isEmpty()) {
            pointsToSet.forEach(p -> pointer.getPointsToSet().addObject(p));
            this.pointerFlowGraph.getSuccsOf(pointer).forEach(
                sp -> {
                    this.workList.addEntry(sp, pointsToSet);
                }
            );
        }

        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        var.getInvokes().forEach(invoke -> {
            JMethod m = this.resolveCallee(recv, invoke);

            if (!m.isStatic()) {
                Pointer p = this.pointerFlowGraph.getVarPtr(m.getIR().getThis());
                this.workList.addEntry(p, new PointsToSet(recv));
            }
            if (!this.callGraph.getCalleesOf(invoke).contains(m)) {
                this.callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke.getInvokeExp()), invoke, m));
                this.addReachable(m);

                for (int i = 0; i < invoke.getInvokeExp().getArgCount(); i++) {
                    Var arg = invoke.getInvokeExp().getArg(i);
                    Var par = m.getIR().getParam(i);
                    this.addPFGEdge(this.pointerFlowGraph.getVarPtr(arg), this.pointerFlowGraph.getVarPtr(par));
                }

                if (invoke.getResult() != null) {
                    m.getIR().getReturnVars().forEach(ret -> {
                        this.addPFGEdge(this.pointerFlowGraph.getVarPtr(ret), this.pointerFlowGraph.getVarPtr(invoke.getResult()));
                    });
                }
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
