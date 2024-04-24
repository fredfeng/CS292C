// not verified
method Test(len: int, lens: array<int>)
  returns (r: int)
  requires len > 0
{
  var i : int;
  var j : int;
  i := 0;
  while (i < len)
    invariant 0 <= i <= len
  {
    j := 0;
    while (j < lens[i])
      // invariant 0 <= i <= len
      invariant 0 <= j <= lens[i]
    {
      j := j + 1;
    }
    i := i + 1;
  }
  return 0;
}