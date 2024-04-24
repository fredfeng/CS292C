method Incr(x: int) returns (r: int)
  ensures r == x + 1
{
  var result : int;
  result := x + 1;
  return result;
}

// verified
method Foo(x: int) returns (r: int)
  requires (x < 0)
{
  var y : int;
  y := x;
  assert (y == x);
  y := Incr(y);
  assert (y == x + 1);
  return 0;
}

// not verified
method Bar(x: int) returns (r: int)
  requires (x < 0)
{
  var y : int;
  y := x;
  y := Incr(y);
  assert (y == x);
  assert (y == x + 1);
  return 0;
}