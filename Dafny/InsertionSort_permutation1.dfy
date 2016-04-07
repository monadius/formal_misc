predicate permutation(a: seq<int>, a0: seq<int>, perm: seq<int>)
{
  (|perm| == |a| && |perm| == |a0|)
  && (forall k :: 0 <= k < |perm| ==> 0 <= perm[k] < |perm|)
  && (forall k, t :: 0 <= k < t < |perm| ==> perm[k] != perm[t])
  && (forall k :: 0 <= k < |perm| ==> a[k] == a0[perm[k]])
}

method id_perm(a: array<int>) returns (ghost perm: seq<int>)
  requires a != null;
  ensures permutation(a[..], old(a[..]), perm);
{
  var n := a.Length;
  var i := 0;
  perm := [];

  while (i < n)
    invariant i <= n;
    invariant |perm| == i;
    invariant forall k :: 0 <= k < i ==> perm[k] == k;
  {
    perm := perm + [i];
    i := i + 1;
  }
}


method InsertionSort(a:array<int>) returns (ghost perm: seq<int>)
  requires a != null;
//  ensures forall k:: forall l:: 0 <= k <= l < a.Length ==> a[k] <= a[l];
//  ensures permutation(a[..], old(a[..]), perm);
  modifies a;
{
  var i:int := 1;
  perm := id_perm(a);

  assert permutation(a[..], old(a[..]), perm);
  assert |perm| == a.Length;

  while(i < a.Length)
    invariant i <= a.Length;
//    invariant forall k :: forall l :: 0 <= k <= l < i && l < a.Length ==> a[k] <= a[l];
  {
    ghost var pt := perm[i];
    var t:int := a[i];
    var j:int := i - 1;
    while (j >= 0)
//      invariant forall k :: j < k < i ==> t <= a[k];
//      invariant forall k :: forall l :: 0 <= k <= l < i ==> a[k] <= a[l];
//      invariant forall k :: forall l :: j + 1 <= k <= l <= i ==> a[k] <= a[l];
    {
      if (a[j] <= t)
      {
	break;
      }

      perm := perm[j + 1 := perm[j]];

      a[j + 1] := a[j];
      j := j - 1;
    }

    perm := perm[j + 1 := pt];

    a[j + 1] := t;
    i := i + 1;
  }

}
