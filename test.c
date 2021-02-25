
// optimiser 0 / e en 0 quand e est pure n'est pas correct
// si e peut être nulle
int f(int x, int y, int z, int a, int b, int c, int d){
  x = 2;
  return 0;
}

int main() {
  int x;
  x = 2/3;
  x = f(1,2,3,4,5,6,7);
  return 0;
}
