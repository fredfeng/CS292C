method min2d() returns (r: int) {
  var a: array<array<int>>;
  var len: int;
  var lens: array<int>;
  var i : int;
  var j : int;
  var min : int;

  a := *;
  len := *;
  lens := *;

  assume len > 0;
  assume lens[0] > 0;
  assume forall i :: 0 <= i < len ==> lens[i] >= 0;

  min := a[0][0];
  i := 0;
  while (i < len)
    invariant 0 <= i <= len
    invariant
      forall x :: 0 <= x < i ==> forall y :: 0 <= y < lens[x] ==> min <= a[x][y]
  {
    j := 0;
    while (j < lens[i])
      invariant 0 <= j <= lens[i]
      invariant
        forall x ::
          0 <= x < i ==>
            forall y::
              0 <= y < lens[x] ==>
                min <= a[x][y]
      invariant
        forall y ::
          0 <= y < j ==>
            min <= a[i][y]
    {
      if a[i][j] < min {
        min := a[i][j];
      } else { }
      j := j + 1;
    }
    i := i + 1;
  }

  assert forall i::
      0 <= i < len ==>
        forall j::
          0 <= j < lens[i] ==>
            min <= a[i][j];

  return 0;
}