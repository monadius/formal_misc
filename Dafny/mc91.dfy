// McCarthy 91 function
// Author: Alexey Solovyev

method mc91(n: nat) returns (b: nat)
  requires n <= 101;
  ensures b == 91; 
{
  var m, c;
  c := 1;
  m := n;
  while (c > 0)
    invariant m <= 111;
    invariant m > 100 && c == 1 ==> m == 101;
    invariant c == 0 ==> m == 91;
    decreases 21 * c + (400 - 2 * m);
  {
    if (m > 100) {
      m := m - 10;
      c := c - 1;
    }
    else {
      m := m + 11;
      c := c + 1;
    }
  }
  
  return m;
}
