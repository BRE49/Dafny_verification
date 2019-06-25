method Reverse(a: array?<int>)
  requires a != null;
  modifies a;
  ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
{
  var l := a.Length - 1;
  var i := 0;
  while (i < (l+1)/2)
    invariant 0 <= i <= (l+1)/2;
    invariant forall k :: 0 <= k < i || l-i < k <= l ==> a[k] == old(a[l-k]);
    invariant forall k :: i <= k <= l-i ==> a[k] == old(a[k]);
  {
    var h := a[i]; a[i] := a[l-i]; a[l-i] := h;
    i := i + 1;
  }
}

method Main() {
  var a := new int[5];
  a[0] := 12;
  a[1] := 3;
  a[2] := 5;
  a[3] := 2;
  a[4] := 1;
  print a[0], " ", a[1], " ", a[2], " ", a[3], " ", a[4], "\n";
  Reverse(a);
  print a[0], " ", a[1], " ", a[2], " ", a[3], " ", a[4], " ";
  
}