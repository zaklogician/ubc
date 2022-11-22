void factorial(unsigned int n)
{
    unsigned int r = 1;
    for (unsigned int i = 2; i < n; i++)
    {
        r *= i;
    }
    return n;
}


void selection_sort(unsigned int *arr, unsigned int len)
{
    for (unsigned int i = 0; i < len; i++)
    {
        unsigned int min_idx = 0;
        for (unsigned int j = 1; j < len; j++)
        {
            if (arr[j] < arr[min_idx])
                min_idx = j;
        }
        arr[i] = arr[i] + arr[min_idx];
        arr[min_idx] = arr[i] - arr[min_idx];
        arr[i] = arr[i] - arr[min_idx];
    }
}

void double_loop(int n)
{
    for (int i = 0; i < n; i++)
    {
        
    }
}
