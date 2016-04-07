% Proving Permutation Properties in Dafny
% Alexey Solovyev

In your latest homework assignment, you were asked to prove that
several sorting procedures yield sorted results:

~~~~~cs
ensures forall k:: forall l:: 0 <= k < l < a.Length ==> a[k] <= a[l];
~~~~~

But this condition is not sufficient to prove that these sorting
procedures sort the input array. Indeed, consider the following method

~~~~~cs
method sort(a:array<int>)
  requires a != null;
  modifies a;
  ensures forall k:: forall l:: 0 <= k < l < a.Length ==> a[k] <= a[l];
{
  var i := 0;
  while (i < a.Length)
    invariant i <= a.Length;
    invariant forall k :: 0 <= k < i ==> a[k] == 0;
  {
    a[i] := 0;
    i := i + 1;
  }
}
~~~~~

Clearly, this method does not sort the input array. But the
postcondition is satisfied. We need another postcondition which
ensures that the input and output arrays are related to each
other. More precisely, we need a postcondition expressing the fact
that the output is a permutation of the input. As an example, consider
the insertion sort method with the following postcondition:

~~~~~cs
method InsertionSort(a:array<int>)
  requires a != null;
  ensures permutation(a[..], old(a[..]));
  modifies a;
{
 ...
}
~~~~~

Here, permutation is a predicate (to be defined shortly). The notation
`a[..]` denotes a slice of the array `a`. In general, we can write
`a[m..n]` to take elements of the array `a` from `m` (inclusive) to
`n` (exclusive). We can also omit lower or upper bounds (or both). In
this case, default lower (`0`) and upper (`a.Length`) bounds will be
used. Hence, `a[..]` returns all elements of the array `a`. The
slicing operation returns sequences, not arrays. Sequences are
immutable and very often they are better suited for writing program
specifications in Dafny. The notation `old(a[..])` denotes all
elements of the input array.

In order to define the predicate `permutation(a, b)`, we first define
the following function:

~~~~~cs
function count(x: int, s: seq<int>): nat
{
  if (|s| == 0) then 
    0
  else if x == s[0] then 
    1 + count(x, s[1..])
  else 
    count(x, s[1..])
}
~~~~~

This function counts the number of occurrences of an element `x` in a
sequence `s`. In Dafny, functions can be used in specifications
only. The permutation predicate can be defined as follows

~~~~~cs
predicate permutation(a: seq<int>, b: seq<int>)
{
  forall t :: count(t, a) == count(t, b)
}
~~~~~

The idea of this definition is simple. Take an arbitrary element `t` and
see how many times it appears in sequences `a` and `b`. If `a` and `b` are
permutations of each other, then `t` should appear the same number of
times in both `a` and `b`.

Let's now try to prove that the result of `InsertionSort` is a
permutation of its input. We add the following invariants:

~~~~~cs
method InsertionSort(a:array<int>)
  requires a != null;
  ensures permutation(a[..], old(a[..]));
  modifies a;
{
  var i:int := 1;

  while(i < a.Length)
    invariant permutation(a[..], old(a[..]));
  {
    ghost var b := a[..];

    var t:int := a[i];
    var j:int := i - 1;
    while (j >= 0)
      invariant forall k :: 0 <= k <= j || i < k < a.Length ==> a[k] == b[k];
      invariant forall k :: j < k < i ==> a[k + 1] == b[k];
    {
      if (a[j] <= t)
      {
        break;
      }

      a[j + 1] := a[j];
      j := j - 1;
    }

    a[j + 1] := t;

    i := i + 1;
  }
}
~~~~~

The invariant in the outer loop (`while(i < a.Length)`) ensures that
the array `a` is a permutation of the input. Invariants in the inner
loop establish relations between the array `a` before the inner loop
(this value is captures in the ghost variable `b`) and after the inner
loop. In Dafny, variables and methods can be declared with the
modifier `ghost`. Ghost variables and methods can only be used in
specifications. They cannot modify regular variables. Dafny can
produce executable files and the compilation process erases all ghost
variables and methods from the compiled code.

After the inner loop and the assignment `a[j + 1] := t`, the following
equations hold (`+` is the concatenation operator for sequences):

~~~~~cs
a[..] == a[..j + 1] + [a[j + 1]] + a[j + 2..i + 1] + a[i + 1..]
b[..] == b[..j + 1] + b[j + 1..i] + [b[i]] + b[i + 1..]
a[j + 1] == b[i]
a[..j + 1] == b[..j + 1]
a[i + 1..] == b[i + 1..]
a[j + 2..i + 1] == b[j + 1..i]
~~~~~

`[a[j + 1]]` and `[b[i]]` denote one-element sequences. Last three
equalities follow directly from the inner loop invariants.

Dafny can prove all these equalities automatically, but it cannot
establish the fact that these equalities imply `permutation(a, b)`. We
need a special auxiliary method (a lemma) to prove this permutation
property. Lemmas in Dafny are regular method with the `ghost` modifier
and with appropriate pre- and postconditions.

First of all, let's prove the following property of the function `count`:

~~~~~cs
count(x, a + b) == count(x, a) + count(x, b);
~~~~~

The first attempt is the following empty method:

~~~~~cs
ghost method count_cat(x: int, a: seq<int>, b: seq<int>)
  ensures count(x, a + b) == count(x, a) + count(x, b);
{
}
~~~~~

Dafny is not able to prove the postcondition automatically. We must
manually guide Dafny to construct an inductive proof of the required
fact:

~~~~~cs
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
~~~~~

You can read more about lemmas and induction in the following Dafny
tutorial:

\url{http://rise4fun.com/Dafny/tutorial/Lemmas}

It is easy to see, that we can use the `count_cat` lemma to establish
the key property which we need to prove `permutation(a,b)`:

~~~~~cs
count(x, a[..]) == count(x, a[..j + 1])
                 + count(x, [a[j + 1]]) 
                 + count(x, a[j + 2..i + 1])
                 + count(x, a[i + 1..])
                == count(x, b[..j + 1])
                 + count(x, [b[i]])
                 + count(x, b[j + 1..i])
                 + count(x, b[i + 1..])
                == count(x, b[..])
~~~~~

It is now left to prove this chain of equalities in Dafny. The proof
is given in the following function (it will be explained later why we
need a function, not a ghost method, and why this function always
returns `true`):

~~~~~cs
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
~~~~~

Preconditions of this function coincide with known properties of our
sequences `a` and `b`. There are two postconditions: the first
postcondition states the key property `count(x, a) == count(x, b)`;
the second postcondition simply tells that the function always returns
`true`. The proof itself is straightforward: first we assert all
equalities between sequences which can be derived from preconditions
(Dafny will fail to prove postconditions if these equalities are not
asserted explicitly). Then we invoke the `count_cat` lemma with
appropriate arguments. Finally, Dafny automatically derives the
required results.

The only thing left is to get rid of the argument `x` in our function
`insert_count`. We want to prove that `count(x, a) == count(x, b)` for any
`x`. The following lemma solves this problem:

~~~~~cs
ghost method insert_perm(a: seq<int>, b: seq<int>, i: int, j: int)
  requires |a| == |b| && 0 <= i < |a| && -1 <= j < i;
  requires a[j + 1] == b[i];
  requires forall k :: 0 <= k <= j || i < k < |a| ==> a[k] == b[k];
  requires forall k :: j < k < i ==> a[k + 1] == b[k];
  ensures permutation(a, b);
{
  assert forall x :: insert_count(x, a, b, i, j) ==> count(x, a) == count(x, b);
}
~~~~~

This lemma has the same preconditions as the `insert_count`
function. The implication

~~~~~cs
insert_count(x, a, b, i, j) ==> count(x, a) == count(x, b)
~~~~~

follows from the postcondition `count(x, a) == count(x, b)` of the
`insert_count` function. Moreover, we also have that `insert_count(x,
a, b, i, j)` is always true hence the implication can be reduced to a
simple fact `count(x, a) == count(x, b)`. This property is under the
universal quantifier, therefore the permutation property follows.

Invoke the `insert_perm` lemma after the assignment `a[j + 1] := t` and
Dafny will be able to finish the proof:

~~~~~cs
method InsertionSort(a:array<int>)
  requires a != null;
  ensures permutation(a[..], old(a[..]));
  modifies a;
{
  var i:int := 1;

  while(i < a.Length)
    invariant permutation(a[..], old(a[..]));
  {
    ghost var b := a[..];

    var t:int := a[i];
    var j:int := i - 1;
    while (j >= 0)
      invariant forall k :: 0 <= k <= j || i < k < a.Length ==> a[k] == b[k];
      invariant forall k :: j < k < i ==> a[k + 1] == b[k];
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
    insert_perm(a[..], b, i, j);

    i := i + 1;
  }
}
~~~~~


