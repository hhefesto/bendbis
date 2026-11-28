import Base
import F64

# the operators and operations on literals, each law by computation
law t.sub:
  {(1.0d - 0.75d : F64.F64) == 0.25d : F64.F64}

def t.sub():
  {==}

law t.div:
  {(1.0d / 3.0d : F64.F64) == 0.3333333333333333d : F64.F64}

def t.div():
  {==}

law t.sqrt:
  {F64.sqrt(2.0d) == 1.4142135623730951d : F64.F64}

def t.sqrt():
  {==}

law t.neg:
  {F64.neg(2.5d) == F64.sub(0.0d, 2.5d) : F64.F64}

def t.neg():
  {==}

law t.le:
  {Bool.and((1.0d <= 1.0d : F64.F64), (2.0d >= 1.0d : F64.F64)) == True{} : Bool}

def t.le():
  {==}

law t.gt:
  {(1.0e-300d > 1.0e-301d : F64.F64) == True{} : Bool}

def t.gt():
  {==}

law t.u32:
  {F64.from_u32(4294967295) == 4294967295.0d : F64.F64}

def t.u32():
  {==}

law t.f32:
  {F64.to_f32(0.1d) == 0.1 : F32}

def t.f32():
  {==}

law t.ulp:
  {(1.0d + 2.220446049250313e-16d : F64.F64) == 1.0000000000000002d : F64.F64}

def t.ulp():
  {==}

law t.tie:
  {(1.0d + 1.1102230246251565e-16d : F64.F64) == 1.0d : F64.F64}

def t.tie():
  {==}

law t.sub0:
  {(4.9e-324d / 2.0d : F64.F64) == 0.0d : F64.F64}

def t.sub0():
  {==}

law t.exp:
  {1.5e3d == 1500.0d : F64.F64}

def t.exp():
  {==}
