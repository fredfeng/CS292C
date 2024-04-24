// verified
method BinarySearch(a: array<int>, len: int, x: int)
  returns (r: int)
  requires len >= 0
  requires
    forall i :: 0 <= i < len ==> forall j :: 0 <= j < len ==> i < j ==> a[i] <= a[j]
  ensures r == 0 || r == 1
  ensures
    r == 1 <==> exists i :: 0 <= i < len && a[i] == x
{
  var lo : int;
  var hi : int;
  var mid : int;
  var found: int;

  lo := 0;
  hi := len;
  found := 0;

  while lo < hi && found == 0
    invariant 0 <= lo <= hi <= len
    invariant found == 0 || found == 1
    invariant
      forall i ::
        0 <= i < lo || hi <= i < len ==> a[i] != x
    invariant found == 1 ==> exists i :: 0 <= i < len && a[i] == x
  {
    mid := lo/2 + hi/2;
    if x == a[mid] {
      found := 1;
    } else {
      if x < a[mid] {
        hi := mid;
      } else {
        lo := mid; // lo := mid + 1;
      }
    }
  }
  assert lo >= hi || found == 1;
  return found;
}
