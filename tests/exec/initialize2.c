

int main() {
  int x;
  x = 65;
  {
    int x = 65;
    x = x + 1;
    {
        int x = (x = 66+1); //It should be the same x.
        x = x + 1;
        putchar(x);
    }
    putchar(x);

  }
  putchar(x);
  putchar(10);
  return 0;
}
