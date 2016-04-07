method LinearSearch(a:array<int>, l:int, u:int, e:int) returns (r:bool)
  requires a != null;
  requires 0 <= l;
  requires u < a.Length;
  ensures r <==> exists k :: l <= k && k <= u && a[k] == e;
{
  var i := l;
  r := false;
  while (i <= u)
    invariant !r <==> (forall k :: l <= k < i && k <= u ==> a[k] != e);
  {
    if (a[i] == e)
    {
      r := true;
      return;
    }
    i := i + 1;
  }
}
