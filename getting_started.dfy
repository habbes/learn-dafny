method Abs(x: int) returns (y: int)
    ensures 0 <= y
{
    if x < 0 {
        return -x;
    } else {
        return x;
    }
}

method MultipleReturns(x: int, y: int) returns (more: int, less: int)
    requires 0 < y
    ensures less < x < more
{
    more := x + y;
    less := x - y;
}

method Max(a: int, b: int) returns (max: int)
    ensures max >= a && max >= b
{
    if a < b {
        max := b;
    } else {
        max := a;
    }
}

method Testing()
{
    var v := Abs(3);
    assert 0 <= v;
}

method TestMax()
{
    /* This method fails verification because the assertions do not hold

    getting_started.dfy(39,4): Error: assertion might not hold
    |
    |     assert v == 5;
    |     ^^^^^^^^^^^^^^

    getting_started.dfy(41,4): Error: assertion might not hold
    |
    |     assert v == 5;
    |     ^^^^^^^^^^^^^^

    getting_started.dfy(43,4): Error: assertion might not hold
    |
    |     assert v == 3;
    |     ^^^^^^^^^^^^^^
   */
    // var v := Max(3, 5);
    // assert v == 5;
    // v := Max(5, 3);
    // assert v == 5;
    // v := Max(3, 3);
    // assert v == 3;

    // But this assertion holds
    var v := Max(3, 5);
    assert v >= 3 && v >= 5;
}