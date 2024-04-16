method MaxInductionHelper(a: array<int>, i: int, len: int)
  returns (r: int)
  requires len > 0
  requires 0 <= i < len
  ensures forall j :: i <= j < len ==> a[j] <= r
  ensures exists j :: i <= j < len && a[j] == r
{
  var result : int;
  var prev : int;

  if i == len - 1 {
    result := a[i];
  } else {
    result := MaxInductionHelper(a, i + 1, len);
    if a[i] > result {
      result := a[i];
    } else {}
  }
  return result;
}

method MaxInduction(a: array<int>, len: int)
  returns (r: int)
  requires len > 0
  ensures forall i :: 0 <= i < len ==> a[i] <= r
  ensures exists i :: 0 <= i < len && a[i] == r
{
  var result: int;
  result := MaxInductionHelper(a, 0, len);
  return result;
}

method MaxIterHelper(a: array<int>, i: int, curr: int, len: int)
  returns (r: int)
  requires len >= 0
  requires 0 <= i <= len
  requires forall j :: 0 <= j < i ==> a[j] <= curr
  requires exists j :: 0 <= j < i && a[j] == curr
  ensures forall i :: 0 <= i < len ==> a[i] <= r
  ensures exists i :: 0 <= i < len && a[i] == r
{
  var result : int;
  var next : int;
  if i == len {
    result := curr;
  } else {
    if a[i] > curr {
      next := a[i];
    } else {
      next := curr;
    }
    result := MaxIterHelper(a, i + 1, next, len);
  }
  return result;
}

method MaxIter(a: array<int>, len: int)
  returns (r: int)
  requires len > 0
  ensures forall i :: 0 <= i < len ==> a[i] <= r
  ensures exists i :: 0 <= i < len && a[i] == r
{
  var result : int;
  result := MaxIterHelper(a, 1, a[0], len);
  return result;
}


method Main() returns (r: int) {
  var a: array<int>;
  var i : int;
  var n : int;
  var h : int;
  var result1 : int;
  var result2 : int;

  n := *;
  a := *;
  assume n > 0;

  result1 := MaxInduction(a, n);
  result2 := MaxIter(a, n);
  print result1;
  print result2;
  assert result1 == result2;
  return 0;
}