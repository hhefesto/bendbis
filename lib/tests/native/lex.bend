import Base
import F64  # a comment after the import

# 1.5d in a comment, in a string, in a char, in names: only the literal
# changes
def s() -> String:
  "a \"quoted\" 1.5d and an escaped \\ 2.5d"

def c() -> Char:
  '1'

def v1d() -> U32:
  7

def y() -> U32:
  v1d()

def z() -> F64.F64:
  1.25d

def w() -> F64.F64:
  1.0e-3d

law t.z:
  {(z() + z() : F64.F64) == 2.5d : F64.F64}

def t.z():
  {==}
