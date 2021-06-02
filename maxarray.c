#include <stddef.h>

unsigned maxarray(unsigned a[], int n) {
  int i; unsigned m;
  i = 0;
  m = 0;
  while (i < n) {
    if (a[i] > m)
      m = a[i];
    ++i;
  }
  return m;
}

unsigned myarr[4] = {1, 4, 2, 3};

int main(void) {
  unsigned m;
  m = maxarray(myarr, 4);
  return (int)m;
}
