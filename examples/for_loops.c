unsigned int factorial(unsigned int n)
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

int double_loop(int n)
{
    int k = 0;
    for (int i = 0; i < n; i++)
    {
        k += i;
    }
    int s = 0;
    for (int i = 0; i < k; i++)
    {
        s += i;
    }
    return s;
}

int loop_write_single()
{
    int a = 0;
    for (int i = 0; i < 10; i++)
    {
        int b = a;
        a = a + i;
        a += b;
    }
    return a;
}

int loop_write_nested()
{
    int a = 0;
    for (int i = 0; i < 10; i++)
    {
        for (int j = 0; j < i; j++)
        {
            a += j * i;
        }
    }
    return a;
}

int loop_overwrite_variable()
{
    int a;
    for (int i = 0; i < 10; i++)
    {
        a = 3;
        a += i;
    }
    return a;
}

void invalid_loop(char * foo)
{
    for (int i = 0; foo[i] < 0; i++)
    {}

}

void loop_continue()
{
    for (int i = 0; i < 10;)
    {
        break;
        i++;
    }
}

int loop_call()
{
    return 1;
}

void func_call_loop_condition()
{
    for (int i = 0; i < loop_call(); i++)
    {
        i++;
    }
}

int if_for_loop(int c)
{
    int b = 10;
    if (c)
    {
        int a = 10;
        b += a;
    }
    for (int i = 0; i < loop_call(); i++)
    {
        int a = 2;
        b -= a;
    }
    return b;
}

int for_scope()
{
    int b = 0;
    {
        int a = 10;
        b += a;
    }
    for (int i = 0; i < 10; i++)
    {
        int a = 20;
        i += a;
    }
    return b;
}


typedef struct
{
    int a;
    int b;
} foo_t;

extern foo_t foo;

void extern_access()
{
    for (int i = 0; i < foo.b;)
    {
        i <<= 2;
    }
}


// typedef unsigned int word_t;

typedef struct {
    int start;
    int end;
} dummy_t;

typedef struct ndks_boot {
//     // p_region_t reserved[MAX_NUM_RESV_REG];
//     // word_t resv_count;
//     // region_t   freemem[16];
//     // seL4_BootInfo      *bi_frame;
//     // seL4_SlotPos slot_pos_cur;
    dummy_t reserved[1];
    int resv_count;
} ndks_boot_t;

extern ndks_boot_t ndks_boot;

// static void merge_regions(void)
// {
//     /* Walk through reserved regions and see if any can be merged */
//     for (int i = 1; i < ndks_boot.resv_count;) {
//         if (ndks_boot.reserved[i - 1].end == ndks_boot.reserved[i].start) {
//             /* extend earlier region */
//             ndks_boot.reserved[i - 1].end = ndks_boot.reserved[i].end;
//             /* move everything else down */
//             for (int j = i + 1; j < ndks_boot.resv_count; j++) {
//                 ndks_boot.reserved[j - 1] = ndks_boot.reserved[j];
//             }

//             ndks_boot.resv_count--;
//             /* don't increment i in case there are multiple adjacent regions */
//         } else {
//             i++;
//         }
//     }
// }

void merge_regions(void)
{
    /* Walk through reserved regions and see if any can be merged */

    // ndks_boot.resv_count--;

    for (int i = 1; i < ndks_boot.resv_count;) {
        ndks_boot.resv_count--;
    }
}

void merge_regions1(void)
{
    /* Walk through reserved regions and see if any can be merged */

    ndks_boot.resv_count--;
}

void merge_regionspp(void)
{
    for (int i = 1; i < ndks_boot.resv_count;) {
        ndks_boot.resv_count++;
    }
}

ndks_boot_t ndks_boot2;

void global()
{
    for (int i = 1; i < ndks_boot2.resv_count;) {
        ndks_boot2.resv_count++;
    }
}

// void insert_join()
// {
//     int a = 1;
//     int i = 0;
//     while (i < 10)
//     {
//         if (i > 5)
//     }
//     return a;
// }
