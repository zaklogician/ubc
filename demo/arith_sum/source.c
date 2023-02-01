// pre condition (0 <= n <= 100)
int arith_sum(int n)
{
    int s = 0;
    for (int i = 0; i < n; i++)
    // loop invariant (0 <= i <= n && s == (i-1)*i/2)
    {
        s += i;
    }
    return s;
}
