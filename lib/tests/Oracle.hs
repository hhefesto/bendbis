-- lib/tests/Oracle.hs: holds vec.bend's lines (stdin) against the machine's
-- IEEE 754 double (GHC's Double: x86-64 SSE2, round to nearest, ties to
-- even; sqrt is sqrtsd; Float conversions are cvtsd2ss/cvtss2sd). A NaN
-- result passes when the machine's is a NaN (any payload, any sign).
-- Prints each line that differs, then "N lines, M differ"; exits 1 if any
-- differs or no line was read.
module Main (main) where

import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import Data.Word (Word32, Word64)
import GHC.Float (castDoubleToWord64, castFloatToWord32, castWord32ToFloat,
                  castWord64ToDouble, double2Float, float2Double)
import Numeric (readHex, showHex)
import System.Exit (exitFailure)

hex :: String -> Word32
hex s = case readHex s of
  [(v, "")] -> v
  _ -> error ("not hex: " ++ s)

d64 :: Word32 -> Word32 -> Double
d64 h l = castWord64ToDouble ((fromIntegral h `shiftL` 32) .|. fromIntegral l)

w64 :: Double -> (Word32, Word32)
w64 d = let w = castDoubleToWord64 d in (fromIntegral (w `shiftR` 32), fromIntegral (w .&. 0xffffffff))

-- the expected (rhi, rlo), and whether a NaN of any bits passes
expect :: String -> Double -> Double -> Word32 -> (Bool, (Word32, Word32))
expect op a b alo = case op of
  "add"  -> f (a + b)
  "sub"  -> f (a - b)
  "mul"  -> f (a * b)
  "div"  -> f (a / b)
  "sqrt" -> f (sqrt a)
  "lt"   -> (False, (0, fromBool (a < b)))
  "le"   -> (False, (0, fromBool (a <= b)))
  "eq"   -> (False, (0, fromBool (a == b)))
  "s2d"  -> f (float2Double (castWord32ToFloat alo))
  "d2s"  -> let r = double2Float a in (isNaN r, (0, castFloatToWord32 r))
  _      -> error ("unknown op: " ++ op)
  where
    f r = (isNaN r, w64 r)
    fromBool x = if x then 1 else 0

isNaNBits :: String -> (Word32, Word32) -> Bool
isNaNBits "d2s" (_, l) = isNaN (castWord32ToFloat l)
isNaNBits _ (h, l) = isNaN (d64 h l)

-- a dec line (dec.bend): the decimal I.F e X read as the machine reads it
-- (GHC's read: the exact rational, then fromRational, rounded to nearest,
-- ties to even; past the range Infinity or 0)
decimal :: String -> String -> String -> Double
decimal i f x = read (i ++ "." ++ (if f == "-" then "0" else f) ++ "e" ++ x)

check :: String -> Maybe String
check line = case words line of
  ["dec", i, f, x, rh, rl] ->
    let want = w64 (decimal i f x)
     in if (hex rh, hex rl) == want then Nothing
        else Just (line ++ "   want " ++ showHex (fst want) "" ++ " " ++ showHex (snd want) "")
  [op, ah, al, bh, bl, rh, rl] ->
    let a = d64 (hex ah) (hex al)
        b = d64 (hex bh) (hex bl)
        got = (hex rh, hex rl)
        (nan, want) = expect op a b (hex al)
        ok = if nan then isNaNBits op got else got == want
     in if ok then Nothing
        else Just (line ++ "   want " ++ showHex (fst want) "" ++ " " ++ showHex (snd want) "")
  _ -> Just ("malformed: " ++ line)

main :: IO ()
main = do
  ls <- lines <$> getContents
  let bad = [m | Just m <- map check ls]
  mapM_ putStrLn (take 50 bad)
  putStrLn (show (length ls) ++ " lines, " ++ show (length bad) ++ " differ")
  if null ls || not (null bad) then exitFailure else pure ()
