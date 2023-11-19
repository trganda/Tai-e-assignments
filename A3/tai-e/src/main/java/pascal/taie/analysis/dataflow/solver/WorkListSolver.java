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

import java.util.List;
import java.util.Set;
import java.util.Stack;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Stack<Node> workList = new Stack<>();
        List<Node> temp = cfg.getNodes().stream().toList();
        for (int i = cfg.getNodes().size() - 1; i >= 0; i--) {
            workList.add(temp.get(i));
        }

        while (!workList.isEmpty()) {
            Node node = workList.pop();
            // meet out of all predecessors to the current node's in
            Fact in = result.getInFact(node);
            cfg.getPredsOf(node).forEach(n -> this.analysis.meetInto(result.getOutFact(n), in));
            result.setInFact(node, in);

            // transfer node
            boolean changed = this.analysis.transferNode(node, in, result.getOutFact(node));
            if (changed) {
                // push back to worklist
                workList.add(node);
            }
        }
    }

    /**
     * Implements work-list algorithm of live variable analysis
     * @param cfg
     * @param result
     */
    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Stack<Node> workList = new Stack<>();
        workList.addAll(cfg.getNodes());

        while (!workList.isEmpty()) {
            Node node = workList.pop();
            Fact out = result.getOutFact(node);
            cfg.getSuccsOf(node).forEach(n -> this.analysis.meetInto(result.getInFact(n), out));
            result.setOutFact(node, out);

            boolean changed = this.analysis.transferNode(node, result.getInFact(node), out);
            if (changed) {
                workList.add(node);
            }
        }
    }
}
