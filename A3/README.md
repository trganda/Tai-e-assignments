# 作业 3：死代码检测

本次作业的目标是使用前两节课实现的活跃变量分析和常量传播分析来实现死代码的检测。
死代码是指程序在运行时永远不会被执行的代码，本次作业只考虑两种类型的死代码，即**不可达代码**（unreachable code）和**无用赋值
**（dead assignment），并且不用考虑死代码检测是否会引入新地死代码。

## 实现

根据作业提示，先将前面实现的活跃变量分析和常量传播分析的代码粘贴进来，并实现 `Solver.initializeBackward()` 和
`WorkListSolver.doSolveBackward()`，这是因为活跃变量分析需要用到它们（`Solver.initializeForward()`
和 `WorkListSolver.doSolveForward()` 可从常量传播分析中粘贴过来）。

### Worklist 下的活跃变量分析

下一步需要使用 WorkList 算法的思想在 `WorkListSolver.doSolveBackward()` 中重新实现活跃变量分析。

```java
@Override
protected void doSolveBackward(CFG<Node> cfg,DataflowResult<Node, Fact> result){
    Stack<Node> workList=new Stack<>();
    workList.addAll(cfg.getNodes());

    while(!workList.isEmpty()){
    Node node=workList.pop();
    Fact out=result.getOutFact(node);
    cfg.getSuccsOf(node).forEach(n->this.analysis.meetInto(result.getInFact(n),out));
    result.setOutFact(node,out);

    boolean changed=this.analysis.transferNode(node,result.getInFact(node),out);
    if(changed){
    workList.add(node);
    }
    }
    }
```

### 实现 DeadCodeDetection

下一步就是实现 `DeadCodeDetection#analyze` 方法。根据课程提示，对于**不可达代码**中的分支不可达代码只考虑两类 IR， `If`
和 `Switch`（循环语句会被转换成 `If`）。
所以只考虑类型 `pascal.taie.ir.stmt.If`，`pascal.taie.ir.stmt.SwitchStmt` 和 `pascal.taie.ir.stmt.AssignStmt`。

```java
@Override
public Set<Stmt> analyze(IR ir){
    // obtain CFG
    CFG<Stmt> cfg=ir.getResult(CFGBuilder.ID);
    // obtain result of constant propagation
    DataflowResult<Stmt, CPFact> constants=
    ir.getResult(ConstantPropagation.ID);
    // obtain result of live variable analysis
    DataflowResult<Stmt, SetFact<Var>>liveVars=
    ir.getResult(LiveVariableAnalysis.ID);
    // keep statements (dead code) sorted in the resulting set
    Set<Stmt> deadCode=new TreeSet<>(Comparator.comparing(Stmt::getIndex));

    // data-flow unreachable node
    Set<Stmt> unreachable=new HashSet<>(cfg.getNodes());
    // traversed nodes
    Map<Stmt, Boolean> traversed=new HashMap<>();

    Stack<Stmt> worklist=new Stack<>();
    Stmt entry=cfg.getEntry();
    worklist.add(entry);

    unreachable.remove(entry);

    while(!worklist.isEmpty()){
    Stmt stmt=worklist.pop();
    if(Boolean.TRUE.equals(traversed.putIfAbsent(stmt,true))){
    continue;
    }

    cfg.getOutEdgesOf(stmt).forEach(e->{
    worklist.add(e.getTarget());
    unreachable.remove(e.getTarget());
    });

    if(stmt instanceof If){
    ConditionExp exp=((If)stmt).getCondition();
    Value val=ConstantPropagation.evaluate(exp,constants.getInFact(stmt));
    if(val.isConstant()){
    cfg.getOutEdgesOf(stmt).forEach(e->{
    if((e.getKind()==Edge.Kind.IF_TRUE&&val.getConstant()<=0)||(e.getKind()==Edge.Kind.IF_FALSE&&val.getConstant()>0)){
    // successor is dead code
    worklist.remove(e.getTarget());
    unreachable.add(e.getTarget());
    }
    });
    }
    }else if(stmt instanceof SwitchStmt){
    Var var=((SwitchStmt)stmt).getVar();
    Value val=ConstantPropagation.evaluate(var,constants.getInFact(stmt));
    if(val.isConstant()){
    AtomicBoolean defaultCase=new AtomicBoolean(true);
    AtomicInteger caseVal=new AtomicInteger();
    ((SwitchStmt)stmt).getCaseTargets().forEach(t->{
    if(val.getConstant()==t.first()){
    defaultCase.set(false);
    caseVal.set(t.first());
    }
    });

    if(defaultCase.get()){
    // all cases are unreachable
    ((SwitchStmt)stmt).getCaseTargets().forEach(t->{
    // successor is dead code
    worklist.remove(t.second());
    unreachable.add(t.second());
    });
    }else{
    // only the default case and other cases is unreachable
    ((SwitchStmt)stmt).getCaseTargets().forEach(t->{
    if(t.first()!=caseVal.get()){
    // successor is dead code
    worklist.remove(t.second());
    unreachable.add(t.second());
    }
    });
    Stmt defaultStmt=((SwitchStmt)stmt).getDefaultTarget();
    worklist.remove(defaultStmt);
    unreachable.add(defaultStmt);
    }
    }
    }else if(stmt instanceof AssignStmt<?,?>){
    SetFact<Var> facts=liveVars.getOutFact(stmt);
    stmt.getDef().ifPresent(l->{
    if(l instanceof Var&&!facts.contains((Var)l)){
    unreachable.add(stmt);
    }
    });
    }
    }

    // control flow unreachable node
    unreachable.forEach(n->{
    if(cfg.getExit()!=n){
    deadCode.add(n);
    }
    });

    return deadCode;
    }
```

需要注意的一点是，对于循环语句生成的 `CFG` 是可能包含环的，所以对于已经遍历过的 `Node` 需要忽略。此外，`CFG`
的前后包含两个 `Nop` 节点，用于表示 `Entry` 和 `Exit` 节点，注意不要将它们加入控制流不可达的死代码结果集合中。

课程代码提供的 `DeadCodeDetection#hasNoSideEffect` 方法并没有使用，因为这里假定所有的方法调用都不是死代码。