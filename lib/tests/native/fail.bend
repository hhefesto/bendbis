import Base
import F64

# must fail: 0.1 + 0.2 is not 0.3 in binary64
law t.add:
  {(0.1d + 0.2d : F64.F64) == 0.3d : F64.F64}

def t.add():
  {==}
