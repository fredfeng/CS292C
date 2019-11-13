In this assignment, you need to verify the correctness of the *FindMax* function by providing the missing loop invariants:
```
method FindMax(a: array<int>) returns (max: int, max_index : int)
    requires a.Length > 0
    ensures forall k :: 0 <= k < a.Length ==> a[k] <= max
    ensures 0 <= max_index
    ensures max_index < a.Length
    ensures a[max_index] == max
{
    var index := 0;
    max_index := 0;
    max := a[max_index];
    while index < a.Length
        invariant ???
        invariant ???
    {
        if (max  < a[index])
        {
            max := a[index];
            max_index := index;
        }
        index := index + 1;
     }
}
```                
Before you start this homework, you should go over the [Dafny tutorial](https://rise4fun.com/Dafny/tutorial).
You can debug your code via [Rise4fun](https://rise4fun.com/Dafny/tutorial/Guide) or [VSCode](https://github.com/dafny-lang/dafny/wiki/INSTALL).

Once you are done, please send your max.dfy to cs292cfall19@gmail.com

Happy hacking.

