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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);

        Stack<JMethod> stack = new Stack<>();
        stack.add(entry);
        while (!stack.isEmpty()) {
            JMethod current = stack.pop();
            if (callGraph.addReachableMethod(current)) {
                Set<Invoke> callSites = callGraph.getCallSitesIn(current);
                if (callSites.isEmpty()) {
                    continue;
                }
                callSites.forEach(callSite -> {
                    Set<JMethod> callees = resolve(callSite);
                    if (callees != null) {
                        callees.forEach(callee -> {
                            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, callee));
                            stack.add(callee);
                        });
                    }
                });
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> ret = new HashSet<>();

        MethodRef methodRef = callSite.getMethodRef();
        CallKind callKind = CallGraphs.getCallKind(callSite);

        JMethod m = null;
        switch (callKind) {
            case STATIC, SPECIAL:
                m = dispatch(methodRef.getDeclaringClass(), methodRef.getSubsignature());
                if (m != null) {
                    ret.add(m);
                }
                break;
            case VIRTUAL, INTERFACE:
                JClass clazz = methodRef.getDeclaringClass();
                // find inside the class
                m = dispatch(clazz, methodRef.getSubsignature());
                if (m != null) {
                    ret.add(m);
                }
                // find all subclasses/implementors of the class
                Stack<JClass> stack = new Stack<>();
                stack.addAll(hierarchy.getDirectSubclassesOf(clazz));
                if (clazz.isInterface()) {
                    stack.addAll(hierarchy.getDirectImplementorsOf(clazz));
                    stack.addAll(hierarchy.getDirectSubinterfacesOf(clazz));
                }
                while (!stack.isEmpty()) {
                    JClass c = stack.pop();
                    m = dispatch(c, methodRef.getSubsignature());
                    if (m != null) {
                        ret.add(m);
                    }

                    stack.addAll(hierarchy.getDirectSubclassesOf(c));
                    if (c.isInterface()) {
                        stack.addAll(hierarchy.getDirectImplementorsOf(c));
                        stack.addAll(hierarchy.getDirectSubinterfacesOf(c));
                    }
                }
                break;
        }

        return ret;
    }

    /**
     * Looks up the target method based on given class and the method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod ret = jclass.getDeclaredMethod(subsignature);
        if (ret != null && !ret.isAbstract()) {
            return ret;
        }

        if (jclass.getSuperClass() != null) {
            return dispatch(jclass.getSuperClass(), subsignature);
        }

        return null;
    }
}
