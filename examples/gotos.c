// int func(int a)
// {
//     if (a)
//     {
//         goto end;
//     }
//     return 1;

// end:
//     return 2;
// }

int foo(int a, int b, int c)
{
    if (a)
        goto exit;
    if (b)
        goto cleanupA;
    if (c)
        goto cleanupB;

    /* everything has succeeded */
    return 0;

cleanupB:
    return 1;
cleanupA:
    return 3;
exit:
    return 4;
}
