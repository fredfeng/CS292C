// verified
method Max() returns (r: int) {
  var x: int;
  var y : int;
  var max : int;

  x := *;
  y := *;

  if (x > y) {
    max := x;
  } else {
    max := y;
  }

  assert (max == x || max == y);
  assert (max >= x && max >= y);

  return 0;
}
