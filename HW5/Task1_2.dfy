function fac(x: nat): nat
{
   if x == 0 then 1 else x * fac(x - 1)
}

method Task1_2(x: nat) returns (r: nat)
requires (x >= 0)
ensures (r == fac(x))
{
    var i := 0;
    r := 1;
    while (i < x)
    invariant (i <= x && r == fac(i))
    {
        i := i+1;
        r := r*i;
    }

}