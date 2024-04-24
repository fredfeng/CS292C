// verified
method Main() returns (r: int) {
  var a : array<int>;
  var i : int;
  var n : int;

  n := *;
  assume n >= 10;

  a[0] := 0;
  a[1] := 1;
  i := 2;
  while (i <= n)
    invariant i >= 2
    invariant i <= n+1
    invariant a[0] == 0
    invariant a[1] == 1
    invariant forall j :: 2 <= j < i ==> a[j] == a[j-1] + a[j-2]
  {
    a[i] := a[i-1] + a[i-2];
    i := i + 1;
  }

  assert (a[10] == 55);

  return 0;
}