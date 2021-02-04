module System.Random.SplitMix32

import System.Random
import Data.IORef

||| Generator for splitmix PRNG
export
data SMGen
    = MkGen
        Bits32 -- seed
        Bits32 -- gamma (odd)

||| Create a SMGen with specific seed and gamma (gamma is forced to be odd)
export
makeSMGen : Int -> Int -> SMGen
makeSMGen seed gamma = MkGen (cast seed) (cast gamma `prim__or_Bits32` 1)

{-
================
Helper Functions
================
-}

succBits32 : Bits32 -> Bits32
succBits32 x = if x == 0xffffffff
    then x
    else x + 1

neg : Bits32 -> Bits32
neg x = cast $ the Int 0x100000000 - cast x

xor : Bits32 -> Bits32 -> Bits32
xor = prim__xor_Bits32

and : Bits32 -> Bits32 -> Bits32
and = prim__and_Bits32

shiftR : Bits32 -> Bits32 -> Bits32
shiftR = prim__shr_Bits32

m1 : Bits32
m1 = 0x55555555

m2 : Bits32
m2 = 0x33333333

m4 : Bits32
m4 = 0x0f0f0f0f

popCount : Bits32 -> Bits32
popCount x0 = -- feel free to add this as a primitive
    let x1 = (x0 `shiftR` 1) `and` m1
        x2 = (x1 `and` m2) + ((x1 `shiftR` 2) `and` m2)
        x3 = (x2 + (x2 `shiftR` 4)) `and` m4
        x4 = x3 + (x3 `shiftR` 8)
        x5 = x4 + (x4 `shiftR` 16)
        x6 = x5 + (x5 `shiftR` 32)
    in x6 `and` 0x7f

shiftXor : Bits32 -> Bits32 -> Bits32
shiftXor n w = w `xor` (w `shiftR` n)

shiftXorMult : Bits32 -> Bits32 -> Bits32 -> Bits32
shiftXorMult n k w = shiftXor n w * k

mix32 : Bits32 -> Bits32
mix32 z0 =
    let z1 = shiftXorMult 16 0x85ebca6b z0
        z2 = shiftXorMult 13 0xc2b2ae35 z1
        z3 = shiftXor 16 z2
    in z3

mix32variant13 : Bits32 -> Bits32
mix32variant13 z0 =
    let z1 = shiftXorMult 16 0x69ad6ccb z0
        z2 = shiftXorMult 13 0xcd9ab5b3 z1
        z3 = shiftXor 16 z2
    in z3

mixGamma : Bits32 -> Bits32
mixGamma z0 =
    let z1 = mix32variant13 z0 `xor` 1
        n = popCount (z1 `xor` (z1 `shiftR` 1))
    in if n >= 12
        then z1
        else z1 `xor` 0xaaaaaaaa

{-
==========
Operations
==========
-}

||| Return the next Bits32 and the updated SMGen
export
nextBits32 : SMGen -> (Bits32, SMGen)
nextBits32 (MkGen seed gamma) = (mix32 seed', MkGen seed' gamma)
  where
    seed' : Bits32
    seed' = seed + gamma

||| Return the next Bits32 in range (lo, hi) inclusive and the updated SMGen
export
nextBits32Range : (Bits32, Bits32) -> SMGen -> (Bits32, SMGen)
nextBits32Range (lo, hi) = mapFst (+ lo) . nextBits32R (succBits32 $ cast $ the Int (cast hi - cast lo))
  where
    nextBits32R : Bits32 -> SMGen -> (Bits32, SMGen)
    nextBits32R 0 gen0 = (0, snd (nextBits32 gen0))
    nextBits32R range gen0 =
        let t = assert_total prim__mod_Bits32 (neg range) range
            go : Bits64 -> SMGen -> (Bits32, SMGen)
            go m gen = if (the Bits32 $ cast m) < t
                then (the Bits32 $ cast $ m `prim__shr_Bits64` 32, gen)
                else
                    let (x, gen') = nextBits32 gen
                        m' = the Bits64 $ cast x * cast range
                    in go m' gen'
            xgen : (Bits32, SMGen)
            xgen = nextBits32 gen0
        in go (cast $ fst xgen) (snd xgen)


||| Return the next Bits64 and the updated SMGen
export
nextBits64 : SMGen -> (Bits64, SMGen)
nextBits64 gen0 =
    let (bottom, gen1) = nextBits32 gen0
        (top, gen2) = nextBits32 gen1
    in (cast top `prim__shl_Bits64` 32 + cast bottom, gen2)

||| Return the next Int and the updated SMGen
export
nextInt : SMGen -> (Int, SMGen)
nextInt gen =
    let (bits64, gen') = nextBits64 gen
    in (if bits64 >= 0x7fffffffffffffff
        then negate $ cast $ bits64 + 0x7fffffffffffffff
        else cast bits64
        , gen')

{-
=========
Splitting
=========
-}

||| Return an unrelated SMGen and the updated SMGen
export
splitSMGen : SMGen -> (SMGen, SMGen)
splitSMGen (MkGen seed gamma) =
    (MkGen seed'' gamma, MkGen (mix32 seed') (mixGamma seed''))
  where
    seed' : Bits32
    seed' = seed + gamma
    seed'' : Bits32
    seed'' = seed + gamma

{-
==========
Generation
==========
-}

||| Deterministically create a new SMGen from a seed
export
mkSMGen : Bits32 -> SMGen
mkSMGen seed = MkGen (mix32 seed) goldenGamma -- different from haskell version 
  where
    goldenGamma : Bits32
    goldenGamma = 0x9e3779b9

theSMGen : IORef SMGen
theSMGen = unsafePerformIO $ do
    init <- cast <$> randomRIO (the Int 0, 0xffffffff)
    newIORef (mkSMGen init)

||| Randomly create an SMGen
export
newSMGen : IO SMGen
newSMGen = do
    (newThe, new) <- splitSMGen <$> readIORef theSMGen
    writeIORef theSMGen newThe
    pure new