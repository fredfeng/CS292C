method Main(n: int, m: int) returns (p: int)
  requires n >= 0
  ensures p == n * m
{
  var acc : int;
  var i : int;

  i := 0;
  acc := 0;

  while i < n
    invariant acc == i * m
    invariant i <= n
  {
    acc := acc + m;
    i := i + 1;
  }
  return acc;
}