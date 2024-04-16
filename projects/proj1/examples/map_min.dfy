method Min(a: array<int>, len: int) returns (r: int)
  requires len > 0
  ensures
    forall i :: 0 <= i < len ==> r <= a[i]
{
  var i : int;
  var min : int;

  min := a[0];
  i := 1;
  while (i < len)
    invariant
      forall x :: 0 <= x < i ==> min <= a[x]
  {
    if a[i] < min {
      min := a[i];
    } else {}
    i := i + 1;
  }
  return min;
}

method MapMin(a: array<array<int>>, len: int, lens: array<int>)
  returns (r: array<int>)
  requires len > 0
  requires forall i :: 0 <= i < len ==> lens[i] > 0
  ensures
    forall i ::
      0 <= i < len ==>
        forall j ::
          0 <= j < lens[i] ==>
            r[i] <= a[i][j]
{
  var mins: array<int>;
  var min : int;
  var i : int;

  i := 0;
  while i < len
    invariant
      forall x ::
        0 <= x  < i ==>
          forall j ::
            0 <= j < lens[x] ==>
              mins[x] <= a[x][j]
  {
    min := Min(a[i], lens[i]);
    mins[i] := min;
  }
  return mins;
}
