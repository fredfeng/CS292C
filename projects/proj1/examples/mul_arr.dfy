method Main() returns (r: int) {
  var n : int;
  var m : int;
  var p : array<int>;
  var i : int;

  n := *;
  m := *;

  assume n >= 0;

  p[0] := 0;
  i := 1;

  while i <= n
    invariant forall j :: 0 <= j < i ==> p[j] == j * m
    invariant 1 <= i <= n + 1
  {
    p[i] := p[i-1] + m;
    i := i + 1;
  }

  assert p[n] == n * m;
  assert forall i :: 0 <= i <= n ==> p[i] == i * m;

  return 0;
}