method AbsInitial(x: int) returns (y: int)
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

method Abs(x: int) returns (y: int)
    // we can use a function in pre/post conditions
    ensures y == abs(x)
{
    // We can use a function in a method.
    // Notice that this method is now redundant and unncessary.
    return abs(x);
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

// Using functions, we can express a fibonacci function
// using the "natural" recursive definition.
function fib(n: nat): nat // nat is the set of natural numbers: non-negative integers
{
    if n == 0 then 0
    else if n == 1 then 1
    else fib(n - 1) + fib(n - 2)
}

// However, the recursive implementation is very slow and inefficient.
// in practice. We can define a method to implement something
// more efficient, but use the function to provide a specification
// that proves correctness of the efficient implementation

method ComputeFib(n: nat) returns (b: nat)
    ensures b == fib(n)
{
    if n == 0 { return 0; }

    var i: int := 1;
    var a := 0;
    b := 1;

    while i < n
        invariant 0 < i <= n
        invariant a == fib(i - 1)
        invariant b == fib(i)
    {
        a, b := b, a + b;
        i := i + 1;
    }
}


method m ()
{
  var i := 20;
  while i != 0
    invariant 0 <= i
    decreases i // helps Dafny to prove termination
  {
    i := i - 1; // if I change this to i := i - 2, Dafny will not be able to prove termination
  }
}

method Find(a: array<int>, key: int) returns (index: int)
    // if index is within bounds, it means we have found the key at that index
    ensures 0 <= index ==> index < a.Length && a[index] == key
    // if index < 0, it means we have not found the key
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
    index := -1;

    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        /*
        Dafny does not know that the loop actually covers all the elements. In order to convince Dafny of this,
        we have to write an invariant that says that everything before the current index has already been looked at (and are not the key).
        Just like the postcondition, we can use a quantifier to express this property
        */
        invariant forall k :: 0 <= k < i ==> a[k] != key
    {
        if a[i] == key
        {
            index := i;
            return;
        }

        i := i + 1;
    }
}

method FindIndexOfMax(a: array<int>) returns (index: int)
    requires a.Length > 0
    ensures 0 <= index < a.Length
    ensures forall k :: 0 <= k < a.Length ==> a[index] >= a[k]
{
    index := 0;

    var i := 1;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= index < a.Length
        invariant forall k :: 0 <= k < i ==> a[index] >= a[k]
    {
        if a[i] > a[index]
        {
            index := i;
        }

        i := i + 1;
    }
}