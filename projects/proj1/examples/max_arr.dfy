method Main() returns (r: int) {
  var i : int;
  var a: array<int>;
  var n : int;
  var max : int;

  n := *;
  a := *;
  assume n > 0;
  max := a[0];

  i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant forall j :: 0 <= j < i ==> max >= a[j]
    invariant exists j :: 0 <= j < i && max == a[j]
  {
    if a[i] > max {
      max := a[i];
    } else {}
    i := i + 1;
  }

  assert forall j :: 0 <= j < n ==> max >= a[j];
  assert exists j :: 0 <= j < n && max == a[j];

  return 0;
}