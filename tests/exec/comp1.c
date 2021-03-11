

int main() {
  int x = 2;
  if(x <= 1){putchar('A');}else{putchar('B');} // B

  if(x < 1) {putchar('C');}else{putchar('D');} // D

  if(1 <= x){putchar('E');}else{putchar('F');} // E

  if(1 < x) {putchar('G');}else{putchar('H');} // G

  if(x >= 1){putchar('A');}else{putchar('B');} // A

  if(x > 1) {putchar('C');}else{putchar('D');} // C

  if(1 >= x){putchar('E');}else{putchar('F');} // F

  if(1 > x) {putchar('G');}else{putchar('H');} // H

  if(1 < 2) {putchar('I');}else{putchar('J');} // I

  if(1 <= 2){putchar('K');}else{putchar('L');} // K
  
  if(1 > 2) {putchar('M');}else{putchar('N');} // N

  if(1 >= 2){putchar('O');}else{putchar('P');} // P


  putchar(10);
  return 0;
}
