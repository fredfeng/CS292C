method Mul(len: int, m : int)
  returns (p: array<int>)
  requires len >= 1
  ensures forall n :: 0 <= n < len ==> p[n] == n * m
{
  var i : int;
  var p : array<int>;

  p[0] := 0;
  i := 1;

  while i < len
    invariant forall j :: 0 <= j < i ==> p[j] == j * m
    invariant 1 <= i <= len
  {
    p[i] := p[i-1] + m;
    i := i + 1;
  }
  return p;
}