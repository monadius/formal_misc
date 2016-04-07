predicate sorted_slice(a: array<int>, lo: int, hi: int)
  requires a != null;
  reads a;
{
  forall i, j :: lo <= i < j < hi && 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate sorted(a: array<int>)
  requires a != null;
  reads a;
{
  sorted_slice(a, 0, a.Length)
}

function count(x: int, s: seq<int>): nat
{
  if (|s| == 0)
  then 0
  else if x == s[0]
       then 1 + count(x, s[1..])
       else count(x, s[1..])
}

predicate perm(a: seq<int>, b: seq<int>)
{
  forall t :: count(t, a) == count(t, b)
}

method bubble(a: array<int>)
  requires a != null;
  modifies a;
  ensures sorted(a);
  ensures perm(a[..], old(a[..]));
{
  var i: nat := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length;
    invariant sorted_slice(a, 0, i);
    invariant perm(a[..], old(a[..]));
  {
    pushToRight(a, i);
    i := i + 1;
  }
}

method pushToRight(a: array<int>, i: nat)
  requires a != null && 0 <= i < a.Length;
  requires sorted_slice(a, 0, i);
  modifies a;
  ensures sorted_slice(a, 0, i + 1);
  ensures perm(old(a[..]), a[..]);
{
  var j: nat := i;
  
  while j > 0 && a[j - 1] > a[j]
    invariant 0 <= j <= i;
    invariant sorted_slice(a, 0, j);
    invariant sorted_slice(a, j, i + 1);
    invariant forall k, k' :: 0 <= k < j && j + 1 <= k' < i + 1
    	      	     	      	==> a[k] <= a[k'];
    invariant perm(old(a[..]), a[..]);
  {
    ghost var a_before := a[..];
    swap(a, j - 1, j);
    swap_implies_perm(a_before, a[..], j - 1, j);
    j := j - 1;
  }
}

method swap(a: array<int>, i: nat, j: nat)
  requires a != null && 0 <= i < a.Length && 0 <= j < a.Length;
  modifies a;
  ensures swapped(old(a[..]), a[..], i, j);
{
  var t := a[i];
  a[i] := a[j];
  a[j] := t;
}

predicate swapped(a: seq<int>, b: seq<int>, i: nat, j: nat)
  requires |a| == |b| && 0 <= i < |a| && 0 <= j < |a|;
{
  (forall k :: 0 <= k < |a| && k != i && k != j ==> a[k] == b[k])
  && (b[j] == a[i])
  && (b[i] == a[j])
}

ghost method swap_same(a: seq<int>, b: seq<int>, i: nat, j: nat)
  requires |a| == |b| && 0 <= i < |a| && i == j;
  requires swapped(a, b, i, j);
  ensures a == b;
{
}

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

ghost method count_two(x: int, a: seq<int>, i: nat, j: nat)
  requires 0 <= i < j < |a|;
  ensures count(x, a) == count(x, a[..i]) + count(x, [a[i]])
 	  + count(x, a[i + 1..j]) + count(x, [a[j]]) + count(x, a[j + 1..]);
{
  count_cat(x, a[..i], a[i..]);
  count_cat(x, [a[i]], a[i + 1..]);
  count_cat(x, a[i + 1..j], a[j..]);
  count_cat(x, [a[j]], a[j + 1..]);
  assert a == a[..i] + a[i..];
  assert a[i..] == [a[i]] + a[i + 1..];
  assert a[i + 1..] == a[i + 1..j] + a[j..];
  assert a[j..] == [a[j]] + a[j + 1..];
}

function swap_count(x: int, a: seq<int>, b: seq<int>, i: nat, j: nat): bool
  requires |a| == |b| && 0 <= i < |a| && 0 <= j < |a|;
  requires swapped(a, b, i, j);
  ensures count(x, a) == count(x, b);
  ensures swap_count(x, a, b, i, j);
{
  if i == j then
     swap_same(a, b, i, j);
     true
  else
    if i < j then
      assert(a[..i] == b[..i]);
      assert(a[i + 1..j] == b[i + 1..j]);
      assert(a[j + 1..] == b[j + 1..]);
      assert(a[i] == b[j]);
      assert(a[j] == b[i]);
      count_two(x, a, i, j);
      count_two(x, b, i, j);
      true
    else
      assert(a[..j] == b[..j]);
      assert(a[j + 1..i] == b[j + 1..i]);
      assert(a[i + 1..] == b[i + 1..]);
      assert(a[j] == b[i]);
      assert(a[i] == b[j]);
      count_two(x, a, j, i);
      count_two(x, b, j, i);
      true
}


ghost method swap_implies_perm(a: seq<int>, b: seq<int>, i: nat, j: nat)
  requires |a| == |b| && 0 <= i < |a| && 0 <= j < |a|;
  requires swapped(a, b, i, j);
  ensures perm(a, b);
{
  assert forall x :: swap_count(x, a, b, i, j) ==> count(x, a) == count(x, b);
}

ghost method perm_trans(a: seq<int>, b: seq<int>, c: seq<int>)
  requires perm(a, b) && perm(b, c);
  ensures perm(a, c);
{}