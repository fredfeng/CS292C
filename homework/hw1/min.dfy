method min2D(a: array<array<int>>)
  returns (r: int)
  requires true
  ensures true
{
  var min := a[0][0];
  for i := 0 to a.Length
    invariant true
  {
    for j := 0 to a[i].Length
      invariant true
    {
      if a[i][j] < min {
        min := a[i][j];
      }
    }
  }
  return min;
}