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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        for (Node node : icfg) {
            result.setOutFact(node, analysis.newInitialFact());
            result.setInFact(node, analysis.newInitialFact());
        }
        // initialize entry node of each entry method
        icfg.entryMethods().forEach(m -> {
            result.setOutFact(icfg.getEntryOf(m), analysis.newBoundaryFact(icfg.getEntryOf(m)));
        });
    }

    private void doSolve() {
        List<Node> wl = new LinkedList<>();
        wl.addAll(icfg.getNodes());

        while (!wl.isEmpty()) {
            wl.stream().findFirst().ifPresent(node -> {
                // meet out of all predecessors to the current node's in
                Fact in = result.getInFact(node);
                // meet out of all transferred predecessors to the current node's in
                icfg.getInEdgesOf(node).forEach(e -> {
                    this.analysis.meetInto(analysis.transferEdge(e, result.getOutFact(e.getSource())), in);
                });
                // update in of node
                result.setInFact(node, in);

                // transfer node
                boolean changed = this.analysis.transferNode(node, in, result.getOutFact(node));
                if (changed) {
                    // push successors to wl
                    wl.addAll(icfg.getSuccsOf(node));
                }
                wl.remove(node);
            });
        }
    }
}
