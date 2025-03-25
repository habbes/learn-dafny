method Abs(x: int) return (y: int)
    ensures 0 <= y
{
    if x < 0 {
        return -x;
    } else {
        return x;
    }
}

method MultipleReturns(x: int, y: int) returns (more: int, less: int)
    ensures less < x
    ensures x < more
{
    more := x + y;
    less := x - y;
}