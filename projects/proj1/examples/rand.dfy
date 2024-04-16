method Abs(n: int) returns (r: int)
  ensures
    (n >= 0 && r == n) || (n < 0 && r == -n) {
  var result : int;
  if n >= 0 {
    result := n;
  } else {
    result := -n;
  }
  return result;
}

method RandomInt(lo: int, hi: int) returns (r: int)
  requires lo < hi
  ensures lo <= r <= hi
{
  var result : int;
  result := *;
  result := Abs(result);
  result := result % (hi - lo + 1) + lo;
  return result;
}