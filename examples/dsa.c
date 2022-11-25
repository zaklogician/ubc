int simple(int a)
{
    a += 2;
    a = 4;
    a -= 5;
    return a;
}

int two_vars(int a, int b)
{
    a = a + b;
    b = a - b;
    a = a - b;
    return a + b;
}

int if_join(int cond)
{
    int a = 10;
    if (cond)
    {
        a += 1;
    }
    else
    {
        a -= 4;
    }
    return a;
}

int if_join_different_length(int cond)
{
    int a = 10;
    if (cond)
    {
        a += 1;
    }
    else
    {
        a -= 4;
        a *= 2;
    }
    return a;
}

int if_join_multiple_variables(int cond)
{
    int a = 10;
    int b = 20;
    if (cond)
    {
        a += 1;
        b -= 1;
    }
    else
    {
        a -= 4;
        a -= b + 4;
        a *= 2;
    }
    return a * b;
}

int if_join_multiple_variables_no_ret(int cond)
{
    int a = 10;
    int b = 20;
    if (cond)
    {
        a += 1;
        b -= 1;
    }
    else
    {
        a -= 4;
        a -= b + 4;
        a *= 2;
    }
    return 0;
}



