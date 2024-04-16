method Main() returns (r: int) {
  var x : int;
  var y : int;
  var z : int;
  var i : int;
  var n : int;

  n := *;

  x := 0;
  y := 1;
  z := x + y;
  i := 2;
  while i < n
    invariant z == x + y
  {
    z := x + y;
    x := y;
    y := z;
    z := x + y;
    i := i + 1;
  }
  assert (z == x + y);
  return 0;
}