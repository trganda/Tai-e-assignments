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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.Set;
import java.util.stream.Collectors;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (this.callGraph.contains(csMethod)) {
            return;
        }

        this.callGraph.addReachableMethod(csMethod);
        csMethod.getMethod().getIR().forEach(stmt -> {
            if (stmt instanceof New || stmt instanceof Copy || stmt instanceof Invoke || stmt instanceof FieldStmt) {
                stmt.accept(new StmtProcessor(csMethod));
            }
        });
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private CSObj csObj;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        private void setCsObj(CSObj csObj) {
            this.csObj = csObj;
        }

        @Override
        public Void visit(New stmt) {
            // New
            Var l = stmt.getLValue();
            Obj obj = heapModel.getObj(stmt);
            Context ctx =  contextSelector.selectHeapContext(csMethod, obj);

            workList.addEntry(csManager.getCSVar(context, l),
                PointsToSetFactory.make(csManager.getCSObj(ctx, obj)));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            // Assign
            addPFGEdge(
                csManager.getCSVar(context, stmt.getRValue()),
                csManager.getCSVar(context, stmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {
            // y = x[i]
            addPFGEdge(
                csManager.getArrayIndex(this.csObj),
                csManager.getCSVar(context, stmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(StoreArray stmt) {
            // x[i] = y
            addPFGEdge(
                csManager.getCSVar(context, stmt.getRValue()),
                csManager.getArrayIndex(this.csObj)
            );
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            // should consider static field
            if (stmt.getFieldRef().isStatic()) {
                // y = T.f
                addPFGEdge(
                    csManager.getStaticField(stmt.getFieldRef().resolve()),
                    csManager.getCSVar(context, stmt.getLValue())
                );
            } else {
                // y = x.f
                if (this.csObj != null) {
                    addPFGEdge(
                        csManager.getInstanceField(this.csObj, stmt.getFieldRef().resolve()),
                        csManager.getCSVar(context, stmt.getLValue())
                    );
                }
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            // should consider static field
            if (stmt.getFieldRef().isStatic()) {
                // T.f = y
                addPFGEdge(
                    csManager.getCSVar(context, stmt.getRValue()),
                    csManager.getStaticField(stmt.getFieldRef().resolve())
                );
            } else {
                // x.f = y
                if (this.csObj != null) {
                    addPFGEdge(
                        csManager.getCSVar(context, stmt.getRValue()),
                        csManager.getInstanceField(this.csObj, stmt.getFieldRef().resolve())
                    );
                }
            }
            return null;
        }

        @Override
        public Void visit(Invoke invoke) {
            // abstract the static call as an assignment operation
            if (invoke.isStatic()) {
                JMethod m = resolveCallee(null, invoke);
                Context ctx = contextSelector.selectContext(
                    csManager.getCSCallSite(context, invoke), m);
                CSMethod cm = csManager.getCSMethod(ctx, m);
                CSCallSite cs = csManager.getCSCallSite(context, invoke);

                if (!callGraph.getCalleesOf(cs).contains(cm)) {
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke.getInvokeExp()), cs, cm));
                    addReachable(cm);

                    // transfer arguments
                    for (int i = 0; i < invoke.getInvokeExp().getArgCount(); i++) {
                        Var arg = invoke.getInvokeExp().getArg(i);
                        Var par = m.getIR().getParam(i);
                        addPFGEdge(
                            csManager.getCSVar(context, arg),
                            csManager.getCSVar(ctx, par)
                        );
                    }

                    // transfer return variable
                    if (invoke.getResult() != null) {
                        m.getIR().getReturnVars().forEach(ret -> {
                            addPFGEdge(
                                csManager.getCSVar(ctx, ret),
                                csManager.getCSVar(context, invoke.getResult())
                            );
                        });
                    }
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
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
            WorkList.Entry entry = this.workList.pollEntry();
            PointsToSet diff = this.propagate(entry.pointer(), entry.pointsToSet());

            if (entry.pointer() instanceof CSVar p) {
                diff.forEach(diffObj -> {
                    // processing store and load statement
                    Var var = p.getVar();
                    CSMethod cm = this.csManager.getCSMethod(p.getContext(), var.getMethod());
                    StmtProcessor stmtProcessor = new StmtProcessor(cm);
                    stmtProcessor.setCsObj(diffObj);
                    var.getStoreArrays().forEach(storeArray -> {
                        storeArray.accept(stmtProcessor);
                    });
                    var.getStoreFields().forEach(storeField -> {
                        storeField.accept(stmtProcessor);
                    });
                    var.getLoadArrays().forEach(loadArray -> {
                        loadArray.accept(stmtProcessor);
                    });
                    var.getLoadFields().forEach(loadField -> {
                        loadField.accept(stmtProcessor);
                    });
                    this.processCall(p, diffObj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet diff = PointsToSetFactory.make();
        pointsToSet.forEach(p -> {
            if (!pointer.getPointsToSet().contains(p)) {
                diff.addObject(p);
            }
        });

        if (!diff.isEmpty()) {
            diff.forEach(p -> pointer.getPointsToSet().addObject(p));
            this.pointerFlowGraph.getSuccsOf(pointer).forEach(sp -> {
                this.workList.addEntry(sp, diff);
            });
        }
        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        recv.getVar().getInvokes().forEach(invoke -> {
            JMethod m = this.resolveCallee(recvObj, invoke);
            Context ctx = this.contextSelector.selectContext(
                this.csManager.getCSCallSite(recv.getContext(), invoke),
                recvObj, m);
            if (!m.isStatic()) {
                // transfer this
                Pointer tp = this.csManager.getCSVar(ctx, m.getIR().getThis());
                this.workList.addEntry(tp, PointsToSetFactory.make(recvObj));
            }
            // transfer arguments
            CSMethod cm = this.csManager.getCSMethod(ctx, m);
            CSCallSite cs = this.csManager.getCSCallSite(recv.getContext(), invoke);
            if (!this.callGraph.getCalleesOf(cs).contains(cm)) {
                this.callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke.getInvokeExp()), cs, cm));
                this.addReachable(cm);

                for (int i = 0; i < m.getParamCount(); i++) {
                    CSVar par = this.csManager.getCSVar(ctx, m.getIR().getParam(i));
                    CSVar arg = this.csManager.getCSVar(recv.getContext(), invoke.getInvokeExp().getArg(i));
                    this.addPFGEdge(arg, par);
                }

                if (invoke.getResult() != null) {
                    m.getIR().getReturnVars().forEach(ret -> {
                        CSVar retVar = this.csManager.getCSVar(ctx, ret);
                        CSVar resVar = this.csManager.getCSVar(recv.getContext(), invoke.getResult());
                        this.addPFGEdge(retVar, resVar);
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
