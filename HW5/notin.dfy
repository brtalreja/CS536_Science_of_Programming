method notin(a: seq<int>) returns (r: int)
requires true
ensures (forall i : int :: (i >= 0) && (i < |a|) ==> a[i] != r)
{
    r := 0;
    if |a| == 0
    {
        r := 0;
    }
    else{
        r := a[0];
        var i := 0;
        while (i < |a|)
        invariant (0 <= i <= |a| && forall j : int :: (0 <= j < i) ==> a[j] >= r)
        {
            if a[i] <= r
            {
                r := a[i];
            }
            i := i+1;
        }
    }
    r := r-1;

}