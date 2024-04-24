// verified
method Even(n: int) returns (r: int)
  requires n >= 0
  ensures r == 0 || r == 1
  ensures (n % 2 == 1 - r)
{
  var result: int;
  if n == 0 {
    result := 1;
  } else {
    result := Odd(n - 1);
  }
  return result;
}

method Odd(n: int) returns (r: int)
  requires n >= 0
  ensures r == 0 || r == 1
  ensures (n % 2 == r)
{
  var result: int;
  if n == 0 {
    result := 0;
  } else {
    result := Even(n - 1);
  }
  return result;
}