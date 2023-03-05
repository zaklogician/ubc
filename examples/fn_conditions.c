
struct abc {
  int x;
};


struct abc get_abc(int val) {
  struct abc x;
  x.x = val;
  return x;
}

int main() {
  struct abc x = get_abc(231);
  return x.x;
}
