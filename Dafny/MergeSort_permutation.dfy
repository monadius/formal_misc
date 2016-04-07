function count(x: int, s: seq<int>): nat
{
  if (|s| == 0) then 
    0
  else if x == s[0] then 
    1 + count(x, s[1..])
  else 
    count(x, s[1..])
}

predicate permutation(a: seq<int>, b: seq<int>)
{
  forall t :: count(t, a) == count(t, b)
}

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
  ensures permutation(a1[..], a[..]);
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
  ensures permutation(a1[..], a[..]);
  ensures a1[..] == old(a1[..]);
  decreases u - l;
{
  a := new int[a1.Length];
  assume forall k:: 0 <= k < a1.Length ==> a[k] == a1[k];

  assert a1[..] == a[..];

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

    assert a1[..] == old(a1[..]);
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
  ensures a1[..] == old(a1[..]);
  ensures permutation(a1[..], a[..]);
{
  a := new int[a1.Length];
  assume forall k:: 0 <= k < a1.Length ==> a[k] == a1[k];
  var buf := new int[u-l+1];
  var i:int := l;
  var j:int := m + 1;
  var k:int := 0;

  assert a[..] == a1[..];
//  assert permutation(a[..], a1[..]);

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
    invariant permutation(a[l..i] + a[m + 1..j], buf[..k]);
  {
    ghost var buf_prev := buf[..k];
    ghost var i_prev := i;
    ghost var j_prev := j;

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

    if (i > i_prev)
    {
      assert buf[..k] == buf_prev + [a[i_prev]];
      assert a[l..i] + a[m + 1..j] == (a[l..i_prev] + [a[i_prev]]) + a[m + 1..j_prev];

      perm_cat(a[l..i_prev] + a[m + 1..j_prev], [a[i_prev]], buf_prev, [a[i_prev]]);
      perm_ac(buf[..k], a[l..i_prev], a[m + 1..j_prev], [a[i_prev]]);
    }
    else
    {
      assert buf[..k] == buf_prev + [a[j_prev]];
      assert a[l..i] + a[m + 1..j] == (a[l..i_prev] + a[m + 1..j_prev]) + [a[j_prev]];
      
      perm_cat(a[l..i_prev] + a[m + 1..j_prev], [a[j_prev]], buf_prev, [a[j_prev]]);
    }
  }

  assert buf[..k] == buf[..];
  assert a[l..i] + a[m + 1..j] == a[l..u + 1];
  assert a1[..] == a[..];
//  assert permutation(a1[l..u + 1], buf[..]);
  ghost var a1_prev := a1[..];
  ghost var buf_prev := buf[..];

  k := 0;
  while (k < u-l+1)
    invariant k <= u - l + 1;
    invariant forall i :: l <= i < l + k ==> a[i] == buf[i - l];
    invariant sorted(buf, 0, u - l);
    invariant forall i :: 0 <= i < l || u < i < a.Length ==> a[i] == a1[i];
//    invariant sorted(a, l, l + k - 1);
    invariant a1[..] == a1_prev && buf[..] == buf_prev;
  {
    a[l + k] := buf[k];
    k := k + 1;
  }

  assert a[..l] == a1[..l] && a[u + 1..] == a1[u + 1..];
  assert a[l..u + 1] == buf[..];
//  assert permutation(a1[l..u + 1], a[l..u + 1]);
//  assert permutation(a1[..l], a[..l]);
//  assert permutation(a1[u + 1..], a[u + 1..]);

  perm_cat(a1[..l], a1[l..u + 1], a[..l], a[l..u + 1]);
  assert a1[..l] + a1[l..u + 1] == a1[..u + 1];
  assert a[..l] + a[l..u + 1] == a[..u + 1];
//  assert permutation(a1[..u + 1], a[..u + 1]);

  perm_cat(a1[..u + 1], a1[u + 1..], a[..u + 1], a[u + 1..]);
  assert a1[..u + 1] + a1[u + 1..] == a1[..];
  assert a[..u + 1] + a[u + 1..] == a[..];
//  assert permutation(a1[..], a[..]);
}

// Lemmas

ghost method count_cat(x: int, a: seq<int>, b: seq<int>)
  ensures count(x, a + b) == count(x, a) + count(x, b);
{
  if a == []
  {
    assert a + b == b;
  }
  else
  {
    count_cat(x, a[1..], b);
    assert a + b == [a[0]] + (a[1..] + b);
  }
}

function perm_cat_count(x: int, a: seq<int>, b: seq<int>, c: seq<int>, d: seq<int>): bool
  requires count(x, a) == count(x, c);
  requires count(x, b) == count(x, d);
  ensures count(x, a + b) == count(x, c + d);
  ensures perm_cat_count(x, a, b, c, d);
{
  count_cat(x, a, b);
  count_cat(x, c, d);
  true
}

ghost method perm_cat(a: seq<int>, b: seq<int>, c: seq<int>, d: seq<int>)
  requires permutation(a, c);
  requires permutation(b, d);
  ensures permutation(a + b, c + d);
{
  assert forall x :: perm_cat_count(x, a, b, c, d) 
     ==> count(x, a + b) == count(x, c + d);
}

function perm_ac_count(x: int, a: seq<int>, b: seq<int>, c: seq<int>, d: seq<int>): bool
  requires count(x, a) == count(x, (b + c) + d);
  ensures count(x, a) == count(x, (b + d) + c);
  ensures perm_ac_count(x, a, b, c, d);
{
  count_cat(x, b, c);
  count_cat(x, b + c, d);
  count_cat(x, b, d);
  count_cat(x, b + d, c);
  true
}

ghost method perm_ac(a: seq<int>, b: seq<int>, c: seq<int>, d: seq<int>)
  requires permutation(a, (b + c) + d);
  ensures permutation(a, (b + d) + c);
{
  assert forall x :: perm_ac_count(x, a, b, c, d) 
     ==> count(x, a) == count(x, (b + d) + c);
}
