# 作业 6：上下文敏感的指针分析

> 作业链接：https://tai-e.pascal-lab.net/pa6.html

在作业 5 的基础上增加上下文并进行指针分析。作业在原有基础上，提供了 ContextSelector 接口用于实现上下文的选择。

![ContextSelector](https://tai-e.pascal-lab.net/pa6/contextselector-subclasses.png)

为此需要实现 ContextSelector 的 6 个实现类，根据作业提示需要注意一点，对于 k-limit 的上下文，其堆上下文（heap context）的层数为 k-1。以 _2CallSelector 为例 selectHeapContext 方法的实现如下。

```java
public class _2CallSelector implements ContextSelector {
    @Override
    public Context selectHeapContext(CSMethod method, Obj obj) {
        int len = method.getContext().getLength();
        if (len == 0) {
            return getEmptyContext();
        } else {
            return ListContext.make(method.getContext().getElementAt(len - 1));
        }
    }
}
```