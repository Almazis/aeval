extern int __VERIFIER_nondet_int(void);

int main() {
  int a, b, olda;
	a = __VERIFIER_nondet_int();
	b = __VERIFIER_nondet_int();
	while (a >= 7) {
		olda = a;
		a = b;
		b = olda + 1;
	}
	return 0;
}
