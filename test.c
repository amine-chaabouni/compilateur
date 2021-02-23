
// optimiser 0 / e en 0 quand e est pure n'est pas correct
// si e peut être nulle

int main() {
  int x;
  x = 42;
  putchar(0 / (x - x));
  return 0;
}
