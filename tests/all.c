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
