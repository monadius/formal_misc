predicate sorted(a: array<int>)
   requires a != null;
   reads a;
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

predicate sorted_slice(a: array<int>, l:int, h:int)
  requires a != null;
  reads a;
{
  forall j, k :: l <= j < k <= h && 0 <= j && k < a.Length ==> a[j] <= a[k]
}

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
  ensures a[i] == old(a[j]) && a[j] == old(a[i]);
  ensures forall k :: 0 <= k && k < a.Length && k != i && k != j ==> a[k] == old(a[k]);
{
  p := perm[i := perm[j]];
  p := p[j := perm[i]];

  a[i], a[j] := a[j], a[i];
}

method id_perm(a: array<int>) returns (ghost perm: seq<int>)
  requires a != null;
  ensures permutation(a[..], old(a[..]), perm);
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


method bubble(a: array<int>) returns (ghost perm: seq<int>)
  requires a != null;
  modifies a;
  requires a.Length >= 2;
//  ensures sorted(a);
  ensures permutation(a[..], old(a[..]), perm);
{
  var i, n, s;
  perm := id_perm(a);

  n := a.Length;
  s := a.Length > 0;

//  perm := swap(a, 0, 1, old(a[..]), perm);

//  while (n > 0)
//    invariant permutation(a[..], old(a[..]), perm);
//  {
//    perm := swap(a, n - 1, n - 2, old(a[..]), perm);
//    n := n - 1;
//  }


  while (s)
    invariant permutation(a[..], old(a[..]), perm);
//    invariant sorted_slice(a, n, a.Length - 1);
//    invariant forall j, k :: 0 <= j < n && n <= k < a.Length ==> a[j] <= a[k];
//    invariant !s ==> sorted_slice(a, 0, n);
    invariant n > 0 || !s;
    decreases n;
  {
    s := false;
    i := 1;

    while (i <= n - 1)
      invariant 1 <= i && i <= n;
      invariant permutation(a[..], old(a[..]), perm);
      invariant n <= 1 ==> !s;
//      invariant sorted_slice(a, n, a.Length - 1);
//      invariant forall j, k :: 0 <= j < n && n <= k < a.Length ==> a[j] <= a[k];
//      invariant forall j :: 0 <= j <= i - 1 ==> a[j] <= a[i - 1]; 
//      invariant !s ==> sorted_slice(a, 0, i - 1);
    {
      if (i > 0) {
//      if (a[i - 1] > a[i]) {
//      	 assume(1 <= i && i < n);
//	 assume(i < a.Length && i - 1 < a.Length);
//	 assume(permutation(a[..], old(a[..]), perm));
	 ghost var p := perm[(i - 1) := perm[i]];
	 p := p[i := perm[i - 1]];
	 perm := p;
	 a[i - 1], a[i] := a[i], a[i - 1];
	 assert(permutation(a[..], old(a[..]), perm));

//      	 perm := swap(a, i - 1, i, t, perm);
	 s := true;
      }
      else {
      	 perm := perm;
      }

//      assume(permutation(a[..], old(a[..]), perm));      

      i := i + 1;
    }

    n := n - 1;
  }


}
