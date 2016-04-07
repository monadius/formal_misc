// Bubble sort: "constructive" permutation invariant
// Author: Alexey Solovyev

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
    invariant forall k :: 0 <= k && k < i ==> perm[k] == k;
  {
    perm := perm + [i];
    i := i + 1;
  }
}


method push(a: array<int>, n: int, ghost a0: seq<int>, ghost perm: seq<int>) returns (s: bool, ghost p: seq<int>)
  requires a != null;
  requires 0 < n <= a.Length;
  requires sorted_slice(a, n, a.Length - 1);
  requires forall j, k :: 0 <= j < n && n <= k < a.Length ==> a[j] <= a[k];
  requires permutation(a[..], a0, perm);
  modifies a;
  ensures n <= 1 ==> !s;
  ensures permutation(a[..], a0, p);
  ensures sorted_slice(a, n - 1, a.Length - 1);
  ensures forall j, k :: 0 <= j < n - 1 && n - 1 <= k < a.Length ==> a[j] <= a[k];
  ensures !s ==> sorted_slice(a, 0, n - 1);
{
  var i := 1;
  s := false;
  p := perm;

  while (i <= n - 1)
    invariant 1 <= i && i <= n;
    invariant permutation(a[..], a0, p);
    invariant n <= 1 ==> !s;
    invariant sorted_slice(a, n, a.Length - 1);
    invariant forall j, k :: 0 <= j < n && n <= k < a.Length ==> a[j] <= a[k];
    invariant forall j :: 0 <= j <= i - 1 ==> a[j] <= a[i - 1]; 
    invariant !s ==> sorted_slice(a, 0, i - 1);
    {
      if (a[i - 1] > a[i]) {
        ghost var t := p[i];
        p := p[i := p[i - 1]];
        p := p[i - 1 := t];

        a[i - 1], a[i] := a[i], a[i - 1];
        s := true;
      }

      i := i + 1;
    }
}


method bubble(a: array<int>) returns (ghost perm: seq<int>)
  requires a != null;
  modifies a;
  ensures sorted(a);
  ensures permutation(a[..], old(a[..]), perm);
{
  var n: nat;
  var s;
  perm := id_perm(a);

  n := a.Length;
  s := a.Length > 0;

  while (s)
    invariant permutation(a[..], old(a[..]), perm);
    invariant sorted_slice(a, n, a.Length - 1);
    invariant forall j, k :: 0 <= j < n && n <= k < a.Length ==> a[j] <= a[k];
    invariant !s ==> sorted_slice(a, 0, n);
    invariant n > 0 || !s;
    decreases n;
  {
    s, perm := push(a, n, old(a[..]), perm);
    n := n - 1;
  }

}

