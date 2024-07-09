method Task1_1(gas: nat, batt: nat, gas_0: nat) returns (miles: nat)
    requires gas_0 == gas && gas > 0 && batt == 0
    ensures miles >= gas_0 - 1
{
    var Gas := gas;
    var Batt := batt;
    miles := 0;
    var Gas_0 := gas_0;

    while Gas > 1 || Batt > 0
        invariant (Gas >= 0 && Batt >= 0 && miles >= Gas_0 - (Batt + Gas))
        decreases Gas + Batt
    {
        if Batt > 0
        {
            Batt := Batt - 1;
        }
        else
        {
            Gas := Gas - 2;
            Batt := Batt + 1;
        }
        miles := miles + 1;
    }
}
