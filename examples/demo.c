int maths(int a, int b)
{
    if (a)
    {
        a += b;
    }
    else
    {
        b -= a;
    }
    return a * b;
}

int arith_sum(int n)
{
    int s = 0;
    for (int i = 0; i < n; i++)
    {
        s += i;
    }
    return s;
}

