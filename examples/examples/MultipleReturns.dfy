method MultipleReturns(x: int, y: int) returns (more: int, less: int)
   requires 0 < y
   ensures less < x < more
{
   more := x + y;
   less := x - y;
}



method Main() {
  var a: int;
  var b: int;
  a := 3;
  b := 5;
  var minus, plus := MultipleReturns(a, b);
  print "Minus: " , minus, " Plus: ", plus;
}