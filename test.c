struct S { int a; 
struct S *suivant;
struct S *precedent; };

int main() {
  struct S *p;
  p->suivant->precedent = 0;
  return 0;
}
