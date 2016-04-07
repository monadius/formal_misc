// Bubble sort: "non-constructive" permutation invariant
// Author: Alexey Solovyev

// Some ideas are based on the lecture notes:
// http://www.doc.ic.ac.uk/~scd/Dafny_Material/Lectures.pdf

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

function count(x: int, s: seq<int>): nat
{
  if (|s| == 0)
  then 0
  else if x == s[0]
       then 1 + count(x, s[1..])
       else count(x, s[1..])
}

predicate permutation(a: seq<int>, b: seq<int>)
{
  forall t :: count(t, a) == count(t, b)
}

method push(a: array<int>, n: int) returns (s: bool)
  requires a != null;
  requires 0 < n <= a.Length;
  requires sorted_slice(a, n, a.Length - 1);
  requires forall j, k :: 0 <= j < n && n <= k < a.Length ==> a[j] <= a[k];
  modifies a;
  ensures n <= 1 ==> !s;
  ensures permutation(old(a[..]), a[..]);
  ensures sorted_slice(a, n - 1, a.Length - 1);
  ensures forall j, k :: 0 <= j < n - 1 && n - 1 <= k < a.Length ==> a[j] <= a[k];
  ensures !s ==> sorted_slice(a, 0, n - 1);
{
  var i := 1;
  s := false;

  while (i <= n - 1)
    invariant 1 <= i && i <= n;
    invariant permutation(old(a[..]), a[..]);
    invariant n <= 1 ==> !s;
    invariant sorted_slice(a, n, a.Length - 1);
    invariant forall j, k :: 0 <= j < n && n <= k < a.Length ==> a[j] <= a[k];
    invariant forall j :: 0 <= j <= i - 1 ==> a[j] <= a[i - 1]; 
    invariant !s ==> sorted_slice(a, 0, i - 1);
    {
      if (a[i - 1] > a[i]) {
        ghost var a_before := a[..];
	a[i - 1], a[i] := a[i], a[i - 1];
	// Use lemmas to prove permutation(a_before, a)
	assert swapped(a_before, a[..], i - 1, i);
	swap_implies_perm(a_before, a[..], i - 1, i);

        s := true;
      }

      i := i + 1;
    }
}


method bubble(a: array<int>)
  requires a != null;
  modifies a;
  ensures sorted(a);
  ensures permutation(a[..], old(a[..]));
{
  var n: nat;
  var s;
  n := a.Length;
  s := a.Length > 0;

  while (s)
    invariant permutation(a[..], old(a[..]));
    invariant sorted_slice(a, n, a.Length - 1);
    invariant forall j, k :: 0 <= j < n && n <= k < a.Length ==> a[j] <= a[k];
    invariant !s ==> sorted_slice(a, 0, n);
    invariant n > 0 || !s;
    decreases n;
  {
    s := push(a, n);
    n := n - 1;
  }

}


// Lemmas

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
  ensures permutation(a, b);
{
  assert forall x :: swap_count(x, a, b, i, j) ==> count(x, a) == count(x, b);
}
