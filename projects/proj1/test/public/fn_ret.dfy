method Negate(x: int) returns (r: int)
  requires x < 0
  ensures r >= 0
{
  var result : int;
  result := -x;
  return result;
}

// not verified
method Foo(x: int) returns (r: int)
  requires (x < 0)
{
  var y : int;
  y := x;
  y := Negate(y);
  assert y < 0;
  return 0;
}

// verified
method Bar(x: int) returns (r: int)
  requires (x < 0)
{
  var y : int;
  y := x;
  y := Negate(y);
  assert y >= 0;
  return 0;
}