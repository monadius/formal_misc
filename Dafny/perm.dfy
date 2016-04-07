predicate permutation(a: array<int>, a0: array<int>, perm: seq<int>)
  requires a != null && a0 != null;
  reads a;
  reads a0;
{
  (|perm| == a.Length && |perm| == a0.Length)
  && (forall k :: 0 <= k && k < |perm| ==> 0 <= perm[k] && perm[k] < |perm|)
  && (forall k, t :: 0 <= k && k < t && t < |perm| ==> perm[k] != perm[t])
  && (forall k :: 0 <= k && k < |perm| ==> a[k] == a0[perm[k]])
}

method swap(a: array<int>, i: nat, j: nat, ghost a0: array<int>, ghost perm: seq<int>) returns (ghost p: seq<int>)
  modifies a;
  requires a != null;
  requires a0 != null;
  requires i < a.Length && j < a.Length;
//  requires permutation(a, a0, perm);
  ensures a != null;
//  ensures permutation(a, a0, p);
//  ensures old(a[i]) == a[j] && old(a[j]) == a[i];
//  ensures forall k :: 0 <= k && k < a.Length && k != i && k != j ==> old(a[k]) == a[k];
{
//  p := perm[i := perm[j]];
//  p := p[j := perm[i]];
  
  a[i], a[j] := a[j], a[i];
}

