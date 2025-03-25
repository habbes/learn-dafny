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