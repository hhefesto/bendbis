import Base
import F64   # bendbis's F64: F64.F64, F64.add, .., literals like 1.5d

# a comment with 1.5d stays
def s() -> String:
  "1.5d stays in a string"

def x() -> F64.F64:
  1.5d

def tenth() -> F64.F64:
  0.1d

def big() -> F64.F64:
  1.7976931348623157e308d

def tiny() -> F64.F64:
  4.9e-324d

def f(+a: F64.F64, b: F64.F64) -> F64.F64:
  (a + b * a : F64.F64)

law t.add:
  {(0.1d + 0.2d : F64.F64) == 0.30000000000000004d : F64.F64}

def t.add():
  {==}

law t.f:
  {f(1.5d, 2.0d) == 4.5d : F64.F64}

def t.f():
  {==}

law t.lt:
  {(0.1d < 0.2d : F64.F64) == True{} : Bool}

def t.lt():
  {==}

law t.from:
  {F64.from_f32(1.5) == 1.5d : F64.F64}

def t.from():
  {==}
