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

method InsertionSort(a:array<int>)
  requires a != null;
  ensures permutation(a[..], old(a[..]));
  modifies a;
{
  var i:int := 1;

  while(i < a.Length)
    invariant permutation(a[..], old(a[..]));
  {
    ghost var prev_a := a[..];

    var t:int := a[i];
    var j:int := i - 1;
    while (j >= 0)
      invariant forall k :: 0 <= k <= j || i < k < a.Length ==> a[k] == prev_a[k];
      invariant forall k :: j < k < i ==> a[k + 1] == prev_a[k];
    {
      if (a[j] <= t)
      {
	break;
      }

      a[j + 1] := a[j];
      j := j - 1;
    }

    a[j + 1] := t;

    // Lemma
    insert_perm(a[..], prev_a, i, j);

    i := i + 1;
  }
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
    assert a + b == [a[0]] + (a[1..] + b);
    count_cat(x, a[1..], b);
  }
}

function insert_count(x: int, a: seq<int>, b: seq<int>, i: int, j: int): bool
  requires |a| == |b| && 0 <= i < |a| && -1 <= j < i;
  requires a[j + 1] == b[i];
  requires forall k :: 0 <= k <= j || i < k < |a| ==> a[k] == b[k];
  requires forall k :: j < k < i ==> a[k + 1] == b[k];
  ensures count(x, a) == count(x, b);
  ensures insert_count(x, a, b, i, j);
{
  assert a[i + 1..] == b[i + 1..];
  assert a[..j + 1] == b[..j + 1];
  assert a[j + 2..i + 1] == b[j + 1..i];	

  assert a == a[..j + 1] + a[j + 1..];
  assert b == b[..j + 1] + b[j + 1..];
  assert a[j + 1..] == a[j + 1..i + 1] + a[i + 1..];
  assert b[j + 1..] == b[j + 1..i + 1] + b[i + 1..];
  assert a[j + 1..i + 1] == [a[j + 1]] + a[j + 2..i + 1];
  assert b[j + 1..i + 1] == b[j + 1..i] + [b[i]];

  count_cat(x, a[..j + 1], a[j + 1..]);
  count_cat(x, b[..j + 1], b[j + 1..]);
  count_cat(x, a[j + 1..i + 1], a[i + 1..]);
  count_cat(x, b[j + 1..i + 1], b[i + 1..]);
  count_cat(x, [a[j + 1]], a[j + 2..i + 1]);
  count_cat(x, b[j + 1..i], [b[i]]);

  true
}

ghost method insert_perm(a: seq<int>, b: seq<int>, i: int, j: int)
  requires |a| == |b| && 0 <= i < |a| && -1 <= j < i;
  requires a[j + 1] == b[i];
  requires forall k :: 0 <= k <= j || i < k < |a| ==> a[k] == b[k];
  requires forall k :: j < k < i ==> a[k + 1] == b[k];
  ensures permutation(a, b);
{
  assert forall x :: insert_count(x, a, b, i, j) ==> count(x, a) == count(x, b);
}
