import Base
import F64

# a literal past the F64 range stays as written: upstream then reads an
# F32 literal (out of its range too) and refuses it
def big() -> F64.F64:
  1.0e400d
