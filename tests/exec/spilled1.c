
// contribution de Timothée Chauvin (X2017)

int f(int i1, int i2, int i3, int i4, int i5, int i6, int i7, int i8) {
  int i9;
  int i10;
  int i11;
  int i12;
  int i13;
  int i14;
  int i15;
  i9 = 9;
  i10 = 10;
  i11 = 11;
  i12 = 12;
  i13 = 13;
  i14 = 14;
  i15 = 15;
  putchar('A' + i1 * i2 - i3 / i4 / i5 / i6 + i7 - i8 + (i9 == i10) - (i11 < i12) - (i13 <= i14) + (i1 > i2 > i3));
  putchar('A' + -1 * i8 + i1 * i2 * (i3 < i15) - (i14 > i13 + i9) * i2 / i2 * i2 / i2 + -i11 + -(i11 != i11) + i4 + i7);
  putchar('A' + i1 * i2 * (i1 < (i2 != 2) * 4) / i3 * i4 / i5 / i6 + i7 / i8 * i9 + i10 * i11 / i12 + 1 / i13 + 30 / i14 + i7 / (i14 == i14));
  return 0;
}

int main() {
  f(1, 2, 3, 4, 5, 6, 7, 8);
  f(1, 1, 1, 1, 1, 1, 1, 1);
  f(2, 2, 2, 2, 2, 2, 2, 2);
  f(8, 1, 2, 3, 4, 5, 6, 7);
  f(7, 6, 5, 4, 3, 2, 1, 8);
  f(-1, -2, -3, -4, -5, -6, -7, -8);
  f(1, -2, 3, -4, 5, -6, 7, -8);
  putchar('\n');
  return 0;
}
