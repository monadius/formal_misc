predicate sorted(a: array<int>, l: int, u: int)
  requires a != null;
  reads a;
{
  forall i :: forall j :: l <= i < j <= u && 0 <= i && j < a.Length ==> a[i] <= a[j]
}

/*
predicate same(a: array<int>, b: array<int>, l: int, u: int)
  requires a != null && b != null;
  reads a, b;
{
  a.Length == b.Length && 
    forall i :: l <= i < u && 0 <= i < a.Length ==> a[i] == b[i] 
}
*/


method MergeSort(a1:array<int>) returns (a:array<int>)
  requires a1 != null && a1.Length > 0;
  ensures a != null;
  ensures a.Length == a1.Length;
  ensures forall k:: forall l:: 0 <= k < l < a.Length ==> a[k] <= a[l];
{
  a := ms(a1, 0, a1.Length-1);
  return;
}


method ms(a1:array<int>, l:int, u:int) returns (a:array<int>)
  requires a1 != null;
  requires 0 <= l < a1.Length;
  requires 0 <= u < a1.Length;
  ensures a != null;
  ensures a.Length == a1.Length;
  ensures sorted(a, l, u);
  ensures forall i :: 0 <= i < l || u < i < a.Length ==> a[i] == a1[i];
//  ensures same(a, a1, 0, l) && same(a, a1, u + 1, a1.Length);
  decreases u - l;
{
  a := new int[a1.Length];
  assume forall k:: 0 <= k < a1.Length ==> a[k] == a1[k];
  if (l >= u)
  {
    return;
  }
  else
  {
    var m:int := (l + u) / 2;
    a := ms(a, l, m);
    a := ms(a, m+1, u);
    a := merge(a, l, m, u);
    return;
  }
}


method merge(a1:array<int>, l:int, m:int, u:int) returns (a:array<int>)
  requires a1 != null;
  requires 0 <= l <= m <= u < a1.Length;
  requires sorted(a1, l, m);
  requires sorted(a1, m + 1, u);
  ensures a != null;
  ensures a.Length == a1.Length;
  ensures sorted(a, l, u);
  ensures forall i :: 0 <= i < l || u < i < a.Length ==> a[i] == a1[i];
{
  a := new int[a1.Length];
  assume forall k:: 0 <= k < a1.Length ==> a[k] == a1[k];
  var buf := new int[u-l+1];
  var i:int := l;
  var j:int := m + 1;
  var k:int := 0;

  while (k < u-l+1)
//    invariant k <= u - l + 1;
    invariant i + j == k + l + (m + 1);
//    invariant sorted(a, l, m);
//    invariant sorted(a, m + 1, u);
    invariant l <= i <= m + 1;
    invariant m + 1 <= j <= u + 1;
    invariant forall t, r :: 0 <= t < k && j <= r <= u ==> buf[t] <= a[r];
    invariant forall t, r :: 0 <= t < k && i <= r <= m ==> buf[t] <= a[r];
    invariant sorted(buf, 0, k - 1);
    invariant forall k :: 0 <= k < a.Length ==> a[k] == a1[k];
  {
    if (i > m)
    {
      buf[k] := a[j];
      j := j + 1;
    }
    else if (j > u)
    {
      buf[k] := a[i];
      i := i + 1;
    }
    else if (a[i] <= a[j])
    {
      buf[k] := a[i];
      i := i + 1;
    }
    else
    {
      buf[k] := a[j];
      j := j + 1;
    }
    k := k + 1;
  }

  k := 0;
  while (k < u-l+1)
    invariant k <= u - l + 1;
    invariant forall i :: l <= i < l + k ==> a[i] == buf[i - l];
    invariant sorted(buf, 0, u - l);
    invariant forall i :: 0 <= i < l || u < i < a.Length ==> a[i] == a1[i];
//    invariant sorted(a, l, l + k - 1);
  {
    a[l + k] := buf[k];
    k := k + 1;
  }
}

