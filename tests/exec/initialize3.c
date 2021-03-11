
struct initialize
{
  int i;
  int j;
};

int main() {
  int x;
  x = 65;
  struct initialize * ini = sbrk(sizeof(struct initialize));
  int a,b,c,d = x;
  b = b + 1;
  c = c + 2;
  d = d + 3;
  ini->i = d + 1;
  ini->j = ini->i + 1;
  putchar(a);
  putchar(b);
  putchar(c);
  putchar(d);
  putchar(ini->i);
  putchar(ini->j);
  putchar(10);
  return 0;
}
