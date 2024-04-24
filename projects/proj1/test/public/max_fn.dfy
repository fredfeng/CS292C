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