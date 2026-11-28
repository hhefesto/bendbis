import Base
import ./F64.bend as F
import ./SPEC.bend as S

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# OPEN: the laws that delimit F64.bend, op(a, b) == SPEC.bend's op(a, b)
# for every input, stated and not yet proven: `bend lib/OPEN.bend` prints
# SOME PROOFS FAIL (8 TODOs) until each has its proof. tests/spec.bend
# holds them on inputs (the specials' table, every pair, and pseudo-random
# ones), and tests/run.zsh holds F64.bend against the machine's double.
# A law proven moves to LAWS.bend.

law add:
  for a: F.F64
  for b: F.F64
  {F.add(a, b) == S.s.add(a, b) : F.F64}

law sub:
  for a: F.F64
  for b: F.F64
  {F.sub(a, b) == S.s.sub(a, b) : F.F64}

law mul:
  for a: F.F64
  for b: F.F64
  {F.mul(a, b) == S.s.mul(a, b) : F.F64}

law div:
  for a: F.F64
  for b: F.F64
  {F.div(a, b) == S.s.div(a, b) : F.F64}

law sqrt:
  for a: F.F64
  {F.sqrt(a) == S.s.sqrt(a) : F.F64}

law to_f32:
  for a: F.F64
  {F.f32.bits(F.to_f32(a)) == S.s.to_f32(a) : U32}

law is_lt:
  for a: F.F64
  for b: F.F64
  {F.is_lt(a, b) == S.s.lt(a, b) : Bool}

law is_eq:
  for a: F.F64
  for b: F.F64
  {F.is_eq(a, b) == S.s.eq(a, b) : Bool}
