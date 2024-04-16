method Test( len: int, lens: array<int>)
  returns (r: int)
  requires len > 0
{
  var i : int;
  i := 0;
  while (i < len)
    invariant 0 <= i <= len
  {
    i := i + 1;
  }
  return 0;
}