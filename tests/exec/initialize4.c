int f(int b, int r, int a, int v, int o){
    putchar(b);
    putchar(r);
    putchar(a);
    putchar(v);
    putchar(o);
}

int print_bravo(int a){
    int b = a+1;
    int r = a+17;
    int v = a+21;
    int o = a+14;
    f(b,r,a,v,o);
}

int main() {
  int x = 65;
  print_bravo(x);
  putchar(10);
  return 0;
}
