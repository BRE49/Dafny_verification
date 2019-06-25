method Add(x: int, y: int) returns (r: int)
  ensures r == x+y;
{
  r := x;
  if (y < 0) {
    var n := y;
    while (n != 0)
      invariant r == x+y-n && 0 <= -n;
    {
      r := r - 1;
      n := n + 1;
    }
  } else {
    var n := y;
    while (n != 0)
      invariant r == x+y-n && 0 <= n;
    {
      r := r + 1;
      n := n - 1;
    }
  }
}

method Mul(x: int, y: int) returns (r: int)
  ensures r == x*y;
  decreases x < 0, x;
{
  if (x == 0) {
    r := 0;
  } else if (x < 0) {
    r := Mul(-x, y);
    r := -r;
  } else {
    r := Mul(x-1, y);
    r := Add(r, y);
  }
}


method Main() {
  var a: int;
  var b: int;
  a := 3;
  b := 5;
  var add := Add(a, b);
  var mul := Mul(a,b);
  print "Add: ", add;
  print " Mul: ", mul;
}
