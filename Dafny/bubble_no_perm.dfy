// Bubble sort: no permutation invariant
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

method bubble(a: array<int>)
  requires a != null;
  modifies a;
  ensures sorted(a);
{
  var i, n, s;
  n := a.Length;
  s := a.Length > 0;

  while (s)
    invariant sorted_slice(a, n, a.Length - 1);
    invariant forall j, k :: 0 <= j < n && n <= k < a.Length ==> a[j] <= a[k];
    invariant !s ==> sorted_slice(a, 0, n);
    invariant n > 0 || !s;
    decreases n;
  {
    s := false;
    i := 1;
    while (i <= n - 1)
      invariant n <= 1 ==> !s;
      invariant 1 <= i && i <= n;
      invariant sorted_slice(a, n, a.Length - 1);
      invariant forall j, k :: 0 <= j < n && n <= k < a.Length ==> a[j] <= a[k];
      invariant forall j :: 0 <= j <= i - 1 ==> a[j] <= a[i - 1]; 
      invariant !s ==> sorted_slice(a, 0, i - 1);
    {
      if (a[i - 1] > a[i]) {
         a[i - 1], a[i] := a[i], a[i - 1];
	       s := true;
      }
      
      i := i + 1;
    }

    n := n - 1;
  }
}
