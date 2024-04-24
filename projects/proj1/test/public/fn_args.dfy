// verified
method Max(x: int, y: int) returns (r: int)
  ensures r >= x && r >= y
  ensures r == x || r == y
{
  var max : int;
  if (x > y) {
    max := x;
  } else {
    max := y;
  }
  return max;
}

// verified
method Min(x: int, y: int) returns (r: int)
  ensures r <= x && r <= y
  ensures r == x || r == y
{
  var min : int;
  min := Max(-y, -x);
  return -min;
}