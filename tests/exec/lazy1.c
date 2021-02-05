
// pour éviter des otpimisations trop agressives
int any() { int x; return x; }
int zero() { int x; x = 10; while(x) x = x-1; return x; }
int false() { return zero(); }
int true() { return !zero(); }
int fail() { return any() / zero(); }

int main() {
  // &&
  if (true() && true())
    putchar(65);
  if (false() && true())
    putchar(66);
  if (true() && false())
    putchar(66);
  if (false() && false())
    putchar(66);
  if (0 && fail())
    putchar(66);
  if (false() && fail())
    putchar(66);
  putchar(10);
  // ||
  if (true() || true())
    putchar(65);
  if (false() || true())
    putchar(65);
  if (true() || false())
    putchar(65);
  if (false() || false())
    putchar(66);
  if (1 || fail())
    putchar(65);
  if (true() || fail())
    putchar(65);
  putchar(10);
  //
  putchar(65 + (false() && fail()));
  putchar(64 + (true() || fail()));
  putchar(10);
  return 0;
}
