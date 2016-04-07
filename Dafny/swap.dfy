predicate permutation(a: seq<int>, a0: seq<int>, perm: seq<int>)
{
  (|perm| == |a| && |perm| == |a0|)
  && (forall k :: 0 <= k && k < |perm| ==> 0 <= perm[k] && perm[k] < |perm|)
  && (forall k, t :: 0 <= k && k < t && t < |perm| ==> perm[k] != perm[t])
  && (forall k :: 0 <= k && k < |perm| ==> a[k] == a0[perm[k]])
}

method swap(a: array<int>, i: nat, j: nat, ghost a0: seq<int>, ghost perm: seq<int>) returns (ghost p: seq<int>)
  modifies a;
  requires a != null;
  requires i < a.Length && j < a.Length;
  requires permutation(a[..], a0, perm);
  ensures permutation(a[..], a0, p);
  ensures a != null;
{
  p := perm[i := perm[j]];
  p := p[j := perm[i]];

  a[i], a[j] := a[j], a[i];
}

method id_perm(a: array<int>) returns (ghost perm: seq<int>)
  requires a != null;
  ensures permutation(a[..], a[..], perm);
{
  var n := a.Length;
  var i := 0;
  perm := [];

  while (i < n)
    invariant |perm| == i;
    invariant forall k :: 0 <= k && k < i ==> perm[k] == k;
    invariant i < n ==> permutation(a[..i], a[..i], perm);
    invariant i >= n ==> permutation(a[..], a[..], perm);
  {
    perm := perm + [i];
    i := i + 1;
  }
}

method test(a: array<int>) returns (ghost perm: seq<int>)
  requires a != null;
  modifies a;
  requires a.Length >= 2;
{
  perm := id_perm(a);
  assert(permutation(a[..], a[..], perm));

  perm := swap(a, 0, 1, old(a[..]), perm);
  assert(permutation(a[..], old(a[..]), perm));
}
