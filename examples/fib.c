int fib(int n) {
    if(n<2) {
        return n;
    } else {
        return fib(n-1) + fib(n-2);
    }
}

int main()
{
  int n;

  n = 10;
  printf("fib(%d)=%d\n", n, fib(n));
  return 0;
}
