predicate sorted(a: array<int>, l: int, u: int)
  requires a != null;
  reads a;
{
  forall i :: forall j :: l <= i < j <= u && 0 <= i && j < a.Length ==> a[i] <= a[j]
}

function max(a: int, b: int): int
{
  if a > b then a else b
}

method BubbleSort(a:array<int>)
  requires a != null;
  ensures forall k:: forall l:: 0 <= k < l < a.Length ==> a[k] <= a[l];
  modifies a;
{
  var i:int := a.Length - 1;
  while(i > 0)
    invariant sorted(a, max(i, 0), a.Length - 1);
    invariant forall k, l :: 0 <= k <= i && i + 1 <= l < a.Length ==> a[k] <= a[l];
  {
    var j:int := 0;

    while (j < i)
      invariant 0 <= j <= i;
      invariant sorted(a, i, a.Length - 1);
      invariant forall k, l :: 0 <= k <= i && i + 1 <= l < a.Length ==> a[k] <= a[l];
      invariant forall k :: 0 <= k <= j ==> a[k] <= a[j];
    {
      if (a[j] > a[j + 1]) {
        var t:int := a[j];
        a[j] := a[j + 1];
        a[j + 1] := t;
      }
      j := j + 1;
    }
    i := i - 1;
  }
}
