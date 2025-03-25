method Abs(x: int) returns (y: int)
    ensures 0 <= y
    ensures 0 <= x ==> y == x
    ensures x < 0 ==> y == -x
{
    if x < 0 {
        y := -x;
    } else {
        y := x;
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
    ensures max == a || max == b
{
    if a < b {
        max := b;
    } else {
        max := a;
    }
}

method TestAbs()
{
    // We need to capture the
    // value in a local variable
    // before we can use it in a specification verifier like assert.
    var v := Abs(-1);
    assert 0 <= v;
    assert v == 1;
}

method TestMax()
{
    var v := Max(3, 5);
    assert v == 5;
    v := Max(5, 3);
    assert v == 5;
    v := Max(3, 3);
    assert v == 3;
}

function abs(x: int): int
{
    // Functions consist of exactly one expression.
    if x < 0 then -x else x
}

method TestAbsFunction()
{
    // We can use functions directly in specifications.
    // Notice that we don't need to capture the return value in a local variable.
    // Also notice that we can assert the result without specifying
    // preconditions or postconditions on the abs function.
    assert abs(3) == 3;
}