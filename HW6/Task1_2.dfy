method Task1_2(a: array<int>)
modifies a
requires (forall i : int :: (i >= 0) && (i < a.Length) ==> a[i] >= 0)
ensures (forall i : int :: (i >= 0) && (i < a.Length) ==> a[i] == 0)
{
    var i := 0;
    while (i < a.Length)
    invariant (0 <= i <= a.Length && (forall j : int :: (0 <= j < i ==> a[j] == 0)) && (forall k : int :: (i <= k < a.Length ==> a[k] >= 0)))
    decreases a.Length - i
    {
        while a[i] > 0
        invariant (0 <= i <= a.Length && (forall j : int :: (0 <= j < i ==> a[j] == 0)) && (forall k : int :: (i <= k < a.Length ==> a[k] >= 0)))
        decreases a[i]
        {
            a[i] := a[i] - 1;
        }
        i := i + 1;
    }
}
