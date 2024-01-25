# 作业 5：非上下文敏感指针分析

> 作业链接：https://tai-e.pascal-lab.net/pa5.html

本次作业的目标是实现课程中描述的非上下文敏感指针分析。作业在原有的处理规则上，增加了数组类型、静态方法和静态字段的处理方式描述，这一点在实践时需格外注意。

## 实现

根据作业提示，需要实现 `pascal.taie.analysis.pta.ci.Solver` 类中的如下方法，其中 `analyze()` 为 `Worklist` 算法主入口：

- `void addReachable(JMethod)`
- `void addPFGEdge(Pointer,Pointer)`
- `void analyze()`
- `PointsToSet propagate(Pointer,PointsToSet)`
- `void processCall(Var,Obj)`

### 注意事项

`Solver` 类中提供的 `hierarchy` 并未使用到，从测试结果来看它不影响算法的实现。在 `Solver` 中提供了 StmtProcessor 的实例对象，
它是一个访问者模式的实现类，需要自己实现各类方法来处理不同类型的语句。当然你也可以选择采用其它方式

```java
private class StmtProcessor implements StmtVisitor<Void> {

    private Obj obj;

    public void setObj(Obj obj) {
        this.obj = obj;
    }

    @Override
    public Void visit(New stmt) {
        Var l = stmt.getLValue();
        Obj obj = heapModel.getObj(stmt);
        workList.addEntry(pointerFlowGraph.getVarPtr(l), new PointsToSet(obj));
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
    public Void visit(Invoke invoke) {
        // abstract the static call as an assignment operation
        if (invoke.isStatic()) {
            JMethod m = resolveCallee(null, invoke);
            if (!callGraph.getCalleesOf(invoke).contains(m)) {
                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke.getInvokeExp()), invoke, m));
                addReachable(m);

                for (int i = 0; i < invoke.getInvokeExp().getArgCount(); i++) {
                    Var arg = invoke.getInvokeExp().getArg(i);
                    Var par = m.getIR().getParam(i);
                    addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(par));
                }

                if (invoke.getResult() != null) {
                    m.getIR().getReturnVars().forEach(ret -> {
                        addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(invoke.getResult()));
                    });
                }
            }
        }
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
            if (this.obj != null) {
                addPFGEdge(
                    pointerFlowGraph.getInstanceField(this.obj, stmt.getFieldRef().resolve()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue())
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
                pointerFlowGraph.getVarPtr(stmt.getRValue()),
                pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()));
        } else {
            // x.f = y
            if (this.obj != null) {
                addPFGEdge(
                    pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getInstanceField(this.obj, stmt.getFieldRef().resolve()));
            }
        }
        return null;
    }
}
```

静态方法调用和静态实例对象中的字段的 Store、Load 操作的处理需要单独考虑。
在原算法的描述中，`processCall` 是用于处理与变量 `Var` 相关的调用语句的。
所以静态方法的调用不应在此次处理（可以这么做，但有点费力不讨好），对静态方法和静态的处理可以简单的将它们看作是一个 Assign 操作，前者是实参至形参的 Assign，后者是静态字段的 Assign 操作。
为此可以将这部分操作放在 `void addReachable(JMethod method)` 中处理

```java
private void addReachable(JMethod method) {
    if (this.callGraph.contains(method)) {
        return;
    }

    this.callGraph.addReachableMethod(method);
    method.getIR().getStmts().forEach(stmt -> {
        if (stmt instanceof New || stmt instanceof Copy || stmt instanceof Invoke || stmt instanceof FieldStmt) {
            this.stmtProcessor.setObj(null);
            stmt.accept(this.stmtProcessor);
        }
    });
}
```

并配合 `StmtProcessor` 的方法 `visit(Invoke invoke)`、`visit(StoreField stmt)` 和 `visit(LoadField stmt)` 进行处理。由于静态方法调用不涉及 `this` 变量（一个 receiver 对象），所以可以看作是常规赋值操作而无需放在 `processCall` 中处理。