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
    {
        if (max  < a[index])
        {
            max := a[index];
            max_index := index;
        }
        index := index + 1;
     }
}