function power(n:int, e:nat):int
{
   if (e==0) then 1 else n * power(n,e-1)
}

method Power1(n:int, e:nat) returns (p:int)
ensures p==power(n, e);
{   var i:= 0;  
    p:= 1;
    while (i!=e)
    invariant i<=e;
    invariant p==power(n, i);
    {
       i := i+1;
       p := p*n;  
    }   
}



method Main() {
  var a: int;
  var b: nat;
  a := 3;
  b := 34234;
  var c := Power1(a,b);
  print "Result: ", c;
}