method InsertionSort(a:array<int>)
  requires a != null;
  ensures forall k:: forall l:: 0 <= k <= l < a.Length ==> a[k] <= a[l];
  modifies a;
{
  var i:int := 1;

  while(i < a.Length)
    invariant forall k :: forall l :: 0 <= k <= l < i && l < a.Length ==> a[k] <= a[l];
  {
    var t:int := a[i];
    var j:int := i - 1;
    while (j >= 0)
      invariant forall k :: j < k < i ==> t <= a[k];
      invariant forall k :: forall l :: 0 <= k <= l < i ==> a[k] <= a[l];
      invariant forall k :: forall l :: j + 1 <= k <= l <= i ==> a[k] <= a[l];
    {
      if (a[j] <= t)
      {
	break;
      }
      a[j + 1] := a[j];
      j := j - 1;
    }
    a[j + 1] := t;
    i := i + 1;
  }
}
