method BinarySearch(a: array<int>, key: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j];
    ensures -1 <= result < a.Length;
    ensures 0 <= result ==> a[result] == key;
    ensures result == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != key;
  {
    var low := 0;
    var high := a.Length;

    while (low < high)
      invariant 0 <= low <= high <= a.Length;
      invariant forall i :: 0 <= i < low ==> a[i] < key;
      invariant forall i :: high <= i < a.Length ==> key < a[i];
    {
      var mid := low + (high - low) / 2;
      var midVal := a[mid];

      if (midVal < key) {
        low := mid + 1;
      } else if (key < midVal) {
        high := mid;
      } else {
        result := mid; // key found
        return;
      }
    }
    result := -1;  // key not present
  }

method Main() {
  var a := new int[5];
  a[0] := 1;
  a[1] := 3;
  a[2] := 5;
  a[3] := 12;
  a[4] := 16;
  // probati promeniti redosled vrednosti da ne bude sortiran, 
  // prijavice gresku da ne prolazi prvi preduslov
  var b := BinarySearch(a,4);
  print "Index: ", b;
}