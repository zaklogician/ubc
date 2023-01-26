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

int foo(int n, int m) {

    while (n != 0 && n != 1) {
        n += 1;
        n >>= 1;
    }
    m = m + (0x7fffffff * n);
}

int foo3(int n, int m) {
    if (n & 1 == 0) {
      m = m + 1; // you didn't prove there were no overflows here
    }
    n = n + 1; // you didn't prove there were no overflows here
    return 0;
}
