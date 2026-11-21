import Base
import ./Core.bend as C

# bendbis: Bend implemented in Bend. Copyright 2026 HigherOrderCO (upstream
# bendlang/bend) and hhefesto; Apache-2.0, see LICENSE and NOTICE.
#
# LAWS: what bendbis's own functions satisfy, proven in Bend. This first
# set is the quantity algebra the checker's usage rides on (Core's q.add,
# q.join, q.dem: bend.ts's quant_add, quant_join, quant_dem), the facts
# check-lam, check-let and uses_close lean on: - is the unit of both, +
# absorbs, both commute, join is idempotent, and dem keeps - and passes
# any other demand on.

# q.add (quant_add)
# -----------------

law q.add.none_l:
  for q: C.Q
  {C.q.add(C.QN{}, q) == q : C.Q}

def q.add.none_l(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

law q.add.none_r:
  for q: C.Q
  {C.q.add(q, C.QN{}) == q : C.Q}

def q.add.none_r(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

law q.add.comm:
  for a: C.Q
  for b: C.Q
  {C.q.add(a, b) == C.q.add(b, a) : C.Q}

def q.add.comm(a, b):
  match a b:
    case C.QN{} C.QN{}:
      {==}
    case C.QN{} C.QL{}:
      {==}
    case C.QN{} C.QM{}:
      {==}
    case C.QL{} C.QN{}:
      {==}
    case C.QL{} C.QL{}:
      {==}
    case C.QL{} C.QM{}:
      {==}
    case C.QM{} C.QN{}:
      {==}
    case C.QM{} C.QL{}:
      {==}
    case C.QM{} C.QM{}:
      {==}

# two live uses are many: what uses_close reports as "consumed more than once"
law q.add.lone_lone:
  {C.q.add(C.QL{}, C.QL{}) == C.QM{} : C.Q}

def q.add.lone_lone():
  {==}

# q.join (quant_join)
# -------------------

law q.join.none_l:
  for q: C.Q
  {C.q.join(C.QN{}, q) == q : C.Q}

def q.join.none_l(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

law q.join.many_l:
  for q: C.Q
  {C.q.join(C.QM{}, q) == C.QM{} : C.Q}

def q.join.many_l(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

law q.join.idem:
  for q: C.Q
  {C.q.join(q, q) == q : C.Q}

def q.join.idem(q):
  match q:
    case C.QN{}:
      {==}
    case C.QL{}:
      {==}
    case C.QM{}:
      {==}

law q.join.comm:
  for a: C.Q
  for b: C.Q
  {C.q.join(a, b) == C.q.join(b, a) : C.Q}

def q.join.comm(a, b):
  match a b:
    case C.QN{} C.QN{}:
      {==}
    case C.QN{} C.QL{}:
      {==}
    case C.QN{} C.QM{}:
      {==}
    case C.QL{} C.QN{}:
      {==}
    case C.QL{} C.QL{}:
      {==}
    case C.QL{} C.QM{}:
      {==}
    case C.QM{} C.QN{}:
      {==}
    case C.QM{} C.QL{}:
      {==}
    case C.QM{} C.QM{}:
      {==}

# q.dem (quant_dem)
# -----------------

law q.dem.none:
  for qt: C.Q
  {C.q.dem(C.QN{}, qt) == C.QN{} : C.Q}

def q.dem.none(qt):
  {==}

law q.dem.lone:
  for qt: C.Q
  {C.q.dem(C.QL{}, qt) == qt : C.Q}

def q.dem.lone(qt):
  {==}

law q.dem.many:
  for qt: C.Q
  {C.q.dem(C.QM{}, qt) == qt : C.Q}

def q.dem.many(qt):
  {==}

# q.show (quant_show): the three spellings
law q.show.all:
  {[C.q.show(C.QN{}), C.q.show(C.QL{}), C.q.show(C.QM{})] == ["-", "", "+"] : List<&2, String>}

def q.show.all():
  {==}
