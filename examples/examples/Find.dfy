method Find(a: array<int>, key: int) returns (index: int)
   ensures 0 <= index ==> index < a.Length && a[index] == key
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
   index := 0;
   while index < a.Length
      invariant 0 <= index <= a.Length
      invariant forall k :: 0 <= k < index ==> a[k] != key
   {
      if a[index] == key { return; }
      index := index + 1;
   }
   index := -1;
}



method Main() {
  var a := new int[5];
  a[0] := 12;
  a[1] := 3;
  a[2] := 5;
  a[3] := 2;
  a[4] := 1;
  var b := Find(a,5);
  print "Index: ", b;
}