unsigned fact(unsigned n)
{
    unsigned f = 1;
    for (unsigned i = 1; i <= n; i++)
        f *= i;
    return f;
}
