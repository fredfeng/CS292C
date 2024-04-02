method min2D(a: array<array<int>>)
  returns (r: int)
  requires true // replace with your own pre-condition(s)
  ensures true // replace with your own post-condition(s)
{
  var min := a[0][0];
  for i := 0 to a.Length
    invariant true // replace with your own invariant
  {
    for j := 0 to a[i].Length
      invariant true // replace with your own invariant
    {
      if a[i][j] < min {
        min := a[i][j];
      }
    }
  }
  return min;
}