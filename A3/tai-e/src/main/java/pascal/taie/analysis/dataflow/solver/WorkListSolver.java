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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        List<Node> wl = new LinkedList<>(cfg.getNodes());

        while (!wl.isEmpty()) {
            wl.stream().findFirst().ifPresent(node -> {
                // meet out of all predecessors to the current node's in
                Fact in = result.getInFact(node);
                cfg.getPredsOf(node).forEach(n -> this.analysis.meetInto(result.getOutFact(n), in));
                result.setInFact(node, in);

                // transfer node
                boolean changed = this.analysis.transferNode(node, in, result.getOutFact(node));
                if (changed) {
                    // push successors to work list
                    wl.addAll(cfg.getSuccsOf(node));
                }
                wl.remove(node);
            });
        }
    }

    /**
     * Implements work-list algorithm of live variable analysis
     *
     * @param cfg
     * @param result
     */
    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Stack<Node> wl = new Stack<>();
        wl.addAll(cfg.getNodes());

        while (!wl.isEmpty()) {
            Node node = wl.pop();
            Fact out = result.getOutFact(node);
            cfg.getSuccsOf(node).forEach(n -> this.analysis.meetInto(result.getInFact(n), out));
            result.setOutFact(node, out);

            boolean changed = this.analysis.transferNode(node, result.getInFact(node), out);
            if (changed) {
                cfg.getPredsOf(node).forEach(wl::push);
            }
        }
    }
}
