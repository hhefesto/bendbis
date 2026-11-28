import Base

# no `import F64`: G is the identity, and 1.5d means what it means to
# upstream (1.5 applied to d)
def f(x: F32, y: U32) -> F32:
  x

def main() -> F32:
  f(1.5d)
