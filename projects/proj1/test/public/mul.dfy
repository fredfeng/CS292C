// verified
method Main() returns (r: int) {
  var n : int;
  var m : int;
  var p : int;
  var x : int;

  n := *;
  m := *;

  assume n >= 0;

  x := 0;
  p := 0;

  while x < n
    invariant p == x * m
    invariant x <= n
  {
    x := x + 1;
    p := p + m;
  }

  assert p == n * m;

  return 0;
}