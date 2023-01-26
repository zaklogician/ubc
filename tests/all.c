int signed_cast__fail_overflow(int c)
{
    if (c + 32 > 150)
        return 1;
    return 0;
}

int signed_cast(int c)
{
    int offset = 0x7fffffff;
    if (c > offset - 32)
        return -1;
    if (c + 32 > 150)
        return 1;
    return 0;
}

int unsigned_cast(unsigned int c)
{
    unsigned int offset = 65;
    if (c + 32 > offset)
        return 1;
    return 0;
}

int hang()
{
    while (1) {}
}

int used_undefined_variable1__fail()
{
    int a;
    return a + 0;
}

int used_undefined_variable2__fail(int cond)
{
    int a;
    if (cond)
        return a + 0;
    return 0;
}

int used_undefined_variable3__ok(int cond)
{
    int a;
    if (cond)
    {
        if (!cond)
        {
            return a + 1; // can't ever reach here, so we're all good
        }
    }
    return 0;
}


int used_undefined_array_element__ok(int i)
{
    int a[10];
    a[0] = 3;
    a[1] = 1;
    a[2] = 4;
    if (0 <= i && i <= 2)
    {
        return a[i];
    }
    return 0;
}

int used_undefined_array_element__fail_if_i_eq_3(int i)
{
    int a[10];
    a[0] = 3;
    a[1] = 1;
    a[2] = 4;
    if (0 <= i && i <= 3)
    {
        return a[i];
    }
    return 0;
}

int used_undefined_array_element__fail_lots_indices(int i)
{
    int a[10];
    a[0] = 3;
    a[1] = 1;
    a[2] = 4;
    return a[i];
}

// ; loop invariant (0 <= i <= n && s == (i-1)*i/2)
// (define-fun loop_invariant@5 ((loop@4@count (_ BitVec 64)) (i___int@v (_ BitVec 32)) (s___int@v (_ BitVec 32))) Bool (
//     and (bvsle (_ bv0 32) i___int@v)
//         (bvsle i___int@v n___int@v~1)
//         (= s___int@v (
//             bvsdiv (bvmul (bvsub i___int@v (_ bv1 32)) i___int@v)
//                    (_ bv2 32))
//         )
// ))

// ; pre condition (0 <= n && n <= 100)
// (assert (and (bvslt (_ bv0 32) n___int@v~1) (bvslt n___int@v~1 (_ bv100 32))))
int arith_sum___fail_because_missing_invariants(int n)
{
    int s = 0;
    for (int i = 0; i < n; i++)
    {
        s += i;
    }
    return s;
}

int arith_sum_cond___fail_because_missing_invariants(unsigned int n, int fast)
{
    if (fast)
    {
        return n * (n + 1) / 2; // c parser doesn't allow signed division apparently
    }
    else
    {
        int s = 0;
        for (int i = 0; i < n; i++)
        {
            s += i;
        }
        return s;
    }
    return 0;
}
