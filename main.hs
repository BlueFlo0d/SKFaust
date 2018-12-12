{-# LANGUAGE FlexibleInstances,MultiParamTypeClasses #-}

import System.Environment
import Control.Monad.Except
import Control.Applicative
import Data.Maybe
import Data.List
import Data.Bits
import Data.WAVE
import Debug.Trace
import Data.Array
import GHC.Float
data MultipleMonadError e a = MultipleMonadError [e] (Maybe a) deriving (Show)
instance Functor (MultipleMonadError e) where
  fmap a (MultipleMonadError b c) = (MultipleMonadError b (fmap a c))
instance Applicative (MultipleMonadError e) where
  pure a = MultipleMonadError [] (Just a)
  (<*>) (MultipleMonadError a b) (MultipleMonadError c d) = MultipleMonadError (a++c) (b <*> d)
instance Monad (MultipleMonadError e) where
  (>>=) (MultipleMonadError a (Just b)) c = MultipleMonadError (a++d) g where
    (MultipleMonadError d g) = c b
  (>>=) (MultipleMonadError a Nothing) c = MultipleMonadError a Nothing
instance MonadError e (MultipleMonadError e) where
  throwError e = MultipleMonadError [e] Nothing
  catchError a b = a

data FaustTypes = FaustInt | FaustFloat | FaustUndef deriving(Show)
instance Eq FaustTypes where
  FaustInt == FaustInt = True
  FaustFloat == FaustFloat = True
  FaustUndef == _ = True
  _ == FaustUndef = True
  _ == _ = False
data BlockTopoTypes = BlockSeq | BlockPar | BlockSplit | BlockMerge deriving(Show)
data BlockDiagram f = BlockFunc f |
                        BlockTopo BlockTopoTypes (BlockDiagram f) (BlockDiagram f) deriving(Show)

class DynamicArrow k where
  (>>>) :: k -> k -> k
  (***) :: k -> k -> k
  unit :: k
class DynamicArrowoid t where
  (.>>>) :: k -> k -> t k
  (.***) :: k -> k -> t k
  unitoid :: t k

data GeneralArrow f = ArrowFunc f |
                      ArrowCompose (GeneralArrow f) (GeneralArrow f)|
                      ArrowSplit (GeneralArrow f) (GeneralArrow f)|
                      ArrowId deriving (Show)

data GeneralArrowoid f k = ArrowoidFunc f |
                           ArrowoidCompose k k|
                           ArrowoidSplit k k|
                           ArrowoidId deriving (Show)
instance DynamicArrow (GeneralArrow f) where
  (>>>) a b = ArrowCompose a b
  (***) a b = ArrowSplit a b
  unit = ArrowId
instance DynamicArrowoid (GeneralArrowoid f) where
  (.>>>) a b = ArrowoidCompose a b
  (.***) a b = ArrowoidSplit a b
  unitoid = ArrowoidId

data TypeTag t f = TypeTag [t] [t] (GeneralArrowoid f (TypeTag t f)) deriving (Show)

instance (Eq t, Show t) => DynamicArrow (MultipleMonadError String (TypeTag t f)) where
  (>>>) i j = join ((\ x y -> let (TypeTag a b f1) = x
                                  (TypeTag c d f2) = y in
                                let o = (TypeTag a d (x .>>> y)) in
                                  case b == c of
                                    True -> return o
                                    False -> let sb = stripPrefix b c in case sb of
                                      Nothing -> (MultipleMonadError ["Incompatible type in series: "++(show b)++" and "++(show c)] (return o))
                                      Just t -> let a1 = return x
                                                    a2 = return y in
                                        (a1 *** (return (TypeTag t t unitoid))) >>> a2) <$> i <*> j)
  (***) = liftA2 (\x y -> let (TypeTag a b f1) = x
                              (TypeTag c d f2) = y in
                            TypeTag (a ++ c) (b ++ d) (x .*** y))
  unit = return (TypeTag [] [] unitoid)


data FaustIntFloatOps = FaustAdd |
                     FaustSub |
                     FaustMul |
                     FaustDiv |
                     FaustPow deriving (Show)
data FaustLogicOps = FaustLT |
                     FaustLE |
                     FaustGT |
                     FaustGE |
                     FaustEQ |
                     FaustNE deriving (Show)
data FaustIntBinOps = FaustMod |
                      FaustAnd |
                      FaustOr |
                      FaustXor |
                      FaustLeftShift |
                      FaustRightShift deriving (Show)
data FaustBuiltins = FaustIntFloatOp FaustIntFloatOps|
                     FaustIntBinOp FaustIntBinOps|
                     FaustLogicOp FaustLogicOps |
                     FaustCastOp FaustTypes|
                     FaustGen FaustTypes FaustData |
                     FaustRdtable FaustTypes (Array Int FaustData) |
                     FaustRwtable [FaustData] deriving (Show)

data FaustData = FaustDataInt Int|FaustDataFloat Float deriving (Show,Eq)

purgeCandidates :: [MultipleMonadError e a]->([MultipleMonadError e a],Int)
{-
purgeCandidates [x] = let MultipleMonadError l a = x
                      in ([x],length l)
purgeCandidates (x:xs) = let (rs,rn) = purgeCandidates xs
                             MultipleMonadError l a = x in
                           case () of _
                                        | length l > rn -> (rs,rn)
                                        | length l == rn -> ((x:rs),rn)
                                        | otherwise -> ([x],length l)
-}
purgeCandidates [x] = let MultipleMonadError l a = x
                      in ([x],length l)
purgeCandidates (x:xs) = let (rs,rn) = purgeCandidates xs
                             MultipleMonadError l a = x in
                           case () of _
                                        | length l > rn -> (rs,rn)
                                        | length l == 0 && length l == rn -> ((x:rs),rn)
                                        | otherwise -> ([x],length l)

type FaustArrow = GeneralArrow FaustBuiltins

typeFaustArrow :: FaustArrow -> [(MultipleMonadError String (TypeTag FaustTypes FaustBuiltins))]
typeFaustArrow i = case i of
  (ArrowFunc x) -> case x of
                     (FaustIntFloatOp y) -> [return (TypeTag [FaustFloat,FaustFloat] [FaustFloat] (ArrowoidFunc x)),
                                            return (TypeTag [FaustInt,FaustInt] [FaustInt] (ArrowoidFunc x))]
                     (FaustLogicOp y) -> [return (TypeTag [FaustFloat,FaustFloat] [FaustInt] (ArrowoidFunc x)),
                                            return (TypeTag [FaustInt,FaustInt] [FaustInt] (ArrowoidFunc x))]
                     (FaustIntBinOp y) -> [return (TypeTag [FaustInt,FaustInt] [FaustInt] (ArrowoidFunc x))]
                     (FaustCastOp t) ->[return (TypeTag [FaustInt] [t] (ArrowoidFunc x)),return (TypeTag [FaustFloat] [t] (ArrowoidFunc x))]
                     (FaustGen t s) -> [return (TypeTag [] [t] (ArrowoidFunc x))]
                     (FaustRdtable t d) -> [return (TypeTag [FaustInt] [t] (ArrowoidFunc x))]
                     (FaustRwtable _) -> [return (TypeTag [FaustInt,FaustFloat,FaustInt] [FaustFloat] (ArrowoidFunc x)),return (TypeTag [FaustInt,FaustInt,FaustInt] [FaustInt] (ArrowoidFunc x))]

  (ArrowSplit a b) -> fst (purgeCandidates (liftA2 (***) (typeFaustArrow a) (typeFaustArrow b)))
  (ArrowId) -> [return (TypeTag [FaustFloat] [FaustFloat] (ArrowoidId)),return (TypeTag [FaustInt] [FaustInt] (ArrowoidId))]
  (ArrowCompose a b) -> fst (purgeCandidates ( liftA2 (>>>) (typeFaustArrow a) (typeFaustArrow b)))
-- tt = typeFaustArrow (ArrowCompose (ArrowSplit (ArrowFunc (FaustGen FaustFloat "0.1")) (ArrowFunc (FaustGen FaustInt "0.2"))) (ArrowFunc (FaustIntFloatOp FaustAdd)))

type RuntimeFaustStatefulFunc = ([FaustData] -> [FaustData] -> ([FaustData],[FaustData]))
data RuntimeFaustArrow = PureNode Int ([FaustData] -> [FaustData])|
                         StatefulNode Int [FaustData] RuntimeFaustStatefulFunc --(state,signal)
statefulLift :: RuntimeFaustArrow -> RuntimeFaustArrow
statefulLift (PureNode n f) = StatefulNode n [] (\d s -> (d,f s))
statefulLift x = x
instance DynamicArrow RuntimeFaustArrow where
  (>>>) (PureNode an a) (PureNode bn b) = PureNode an (b.a)
  (>>>) (StatefulNode an ad af) (StatefulNode bn bd bf) = StatefulNode an (ad ++ bd) (\d s -> let la = length ad in
                                                                                let (oad,oas) = af (take la d) s in
                                                                                  let (obd,obs) = bf (drop la d) oas in
                                                                                    (oad ++ obd,obs))
  (>>>) x y = (>>>) (statefulLift x) (statefulLift y)
  (***) (PureNode an a) (PureNode bn b) = PureNode (an+bn) (\s -> ((a (take an s)) ++ (b (drop an s))))
  (***) (StatefulNode an ad af) (StatefulNode bn bd bf) = StatefulNode (an+bn) (ad ++ bd) (\d s -> let la = length ad in
                                                                                let (oad,oas) = af (take la d) (take an s) in
                                                                                  let (obd,obs) = bf (drop la d) (drop an s) in
                                                                                    (oad ++ obd,oas ++ obs))
  (***) x y = (***) (statefulLift x) (statefulLift y)
  unit = PureNode 0 id
runArrow :: RuntimeFaustArrow -> [FaustData] -> (RuntimeFaustArrow,[FaustData])
runArrow (StatefulNode n d f) s = let (od,os) = f d s in
                                         (StatefulNode n od f,os)
runArrow (PureNode n f) s = (PureNode n f,f s)

boolToInt :: Bool -> Int
boolToInt True = 1
boolToInt False = 0
getInt :: FaustData -> Int
getInt (FaustDataInt i) = i
getFloat :: FaustData -> Float
getFloat (FaustDataFloat i) = i
faustIntAdd :: [FaustData]->[FaustData]
faustIntAdd [FaustDataInt a,FaustDataInt b] = [FaustDataInt (a+b)]
faustIntSub :: [FaustData]->[FaustData]
faustIntSub [FaustDataInt a,FaustDataInt b] = [FaustDataInt (a-b)]
faustIntMul :: [FaustData]->[FaustData]
faustIntMul [FaustDataInt a,FaustDataInt b] = [FaustDataInt (a*b)]
faustIntDiv :: [FaustData]->[FaustData]
faustIntDiv [FaustDataInt a,FaustDataInt b] = [FaustDataInt (quot a b)]
faustIntPow :: [FaustData]->[FaustData]
faustIntPow [FaustDataInt a,FaustDataInt b] = [FaustDataInt (a^b)]
faustIntMod :: [FaustData]->[FaustData]
faustIntMod [FaustDataInt a,FaustDataInt b] = [FaustDataInt (mod a b)]
faustIntAnd :: [FaustData]->[FaustData]
faustIntAnd [FaustDataInt a,FaustDataInt b] = [FaustDataInt (a .&. b)]
faustIntOr :: [FaustData]->[FaustData]
faustIntOr [FaustDataInt a,FaustDataInt b] = [FaustDataInt (a .|. b)]
faustIntXor :: [FaustData]->[FaustData]
faustIntXor [FaustDataInt a,FaustDataInt b] = [FaustDataInt (xor a b)]
faustIntLeftShift :: [FaustData]->[FaustData]
faustIntLeftShift [FaustDataInt a,FaustDataInt b] = [FaustDataInt (shift a b)]
faustIntRightShift :: [FaustData]->[FaustData]
faustIntRightShift [FaustDataInt a,FaustDataInt b] = [FaustDataInt (shift a (- b))]
faustIntLT :: [FaustData]->[FaustData]
faustIntLT [FaustDataInt a,FaustDataInt b] = [FaustDataInt (boolToInt (a < b))]
faustIntLE :: [FaustData]->[FaustData]
faustIntLE [FaustDataInt a,FaustDataInt b] = [FaustDataInt (boolToInt (a <= b))]
faustIntGT :: [FaustData]->[FaustData]
faustIntGT [FaustDataInt a,FaustDataInt b] = [FaustDataInt (boolToInt (a > b))]
faustIntGE :: [FaustData]->[FaustData]
faustIntGE [FaustDataInt a,FaustDataInt b] = [FaustDataInt (boolToInt (a >= b))]
faustIntEQ :: [FaustData]->[FaustData]
faustIntEQ [FaustDataInt a,FaustDataInt b] = [FaustDataInt (boolToInt (a == b))]
faustIntNE :: [FaustData]->[FaustData]
faustIntNE [FaustDataInt a,FaustDataInt b] = [FaustDataInt (boolToInt (not (a == b)))]

faustFloatAdd :: [FaustData]->[FaustData]
faustFloatAdd [FaustDataFloat a,FaustDataFloat b] = [FaustDataFloat (a+b)]
faustFloatSub :: [FaustData]->[FaustData]
faustFloatSub [FaustDataFloat a,FaustDataFloat b] = [FaustDataFloat (a-b)]
faustFloatMul :: [FaustData]->[FaustData]
faustFloatMul [FaustDataFloat a,FaustDataFloat b] = [FaustDataFloat (a*b)]
faustFloatDiv :: [FaustData]->[FaustData]
faustFloatDiv [FaustDataFloat a,FaustDataFloat b] = [FaustDataFloat (a/b)]
faustFloatPow :: [FaustData]->[FaustData]
faustFloatPow [FaustDataFloat a,FaustDataFloat b] = [FaustDataFloat (a**b)]
faustFloatLT :: [FaustData]->[FaustData]
faustFloatLT [FaustDataFloat a,FaustDataFloat b] = [FaustDataInt (boolToInt (a < b))]
faustFloatLE :: [FaustData]->[FaustData]
faustFloatLE [FaustDataFloat a,FaustDataFloat b] = [FaustDataInt (boolToInt (a <= b))]
faustFloatGT :: [FaustData]->[FaustData]
faustFloatGT [FaustDataFloat a,FaustDataFloat b] = [FaustDataInt (boolToInt (a > b))]
faustFloatGE :: [FaustData]->[FaustData]
faustFloatGE [FaustDataFloat a,FaustDataFloat b] = [FaustDataInt (boolToInt (a >= b))]
faustFloatEQ :: [FaustData]->[FaustData]
faustFloatEQ [FaustDataFloat a,FaustDataFloat b] = [FaustDataInt (boolToInt (a == b))]
faustFloatNE :: [FaustData]->[FaustData]
faustFloatNE [FaustDataFloat a,FaustDataFloat b] = [FaustDataInt (boolToInt (not (a == b)))]

faustIntCounter :: RuntimeFaustStatefulFunc
faustIntCounter [FaustDataInt x] [FaustDataInt y] = ([FaustDataInt (x+y)],[FaustDataInt x])


interpretFaustArrow :: (TypeTag FaustTypes FaustBuiltins)-> RuntimeFaustArrow
interpretFaustArrow (TypeTag t1 t2 (ArrowoidFunc (FaustIntFloatOp op)))
  = PureNode 2 (case t1 of
                   [FaustFloat,FaustFloat] ->
                     case op of
                       FaustAdd -> faustFloatAdd
                       FaustSub -> faustFloatSub
                       FaustMul -> faustFloatMul
                       FaustDiv -> faustFloatDiv
                       FaustPow -> faustFloatPow
                   [FaustInt,FaustInt] ->
                     case op of
                       FaustAdd -> faustIntAdd
                       FaustSub -> faustIntSub
                       FaustMul -> faustIntMul
                       FaustDiv -> faustIntDiv
                       FaustPow -> faustIntPow
               )
interpretFaustArrow (TypeTag _ _ (ArrowoidFunc (FaustIntBinOp op)))
  = PureNode 2 (case op of
                   FaustMod -> faustIntMod
                   FaustAnd -> faustIntAnd
                   FaustOr -> faustIntOr
                   FaustXor -> faustIntXor
                   FaustLeftShift -> faustIntLeftShift
                   FaustRightShift -> faustIntRightShift
                     )
interpretFaustArrow (TypeTag t1 _ (ArrowoidFunc (FaustLogicOp op)))
  = PureNode 2 (case t1 of
                   [FaustFloat,FaustFloat] ->
                     case op of
                       FaustLT -> faustFloatLT
                       FaustLE -> faustFloatLE
                       FaustGT -> faustFloatGT
                       FaustGE -> faustFloatGE
                       FaustEQ -> faustFloatEQ
                       FaustNE -> faustFloatNE
                   [FaustInt,FaustInt] ->
                     case op of
                       FaustLT -> faustIntLT
                       FaustLE -> faustIntLE
                       FaustGT -> faustIntGT
                       FaustGE -> faustIntGE
                       FaustEQ -> faustIntEQ
                       FaustNE -> faustIntNE
               )
interpretFaustArrow (TypeTag t1 t2 (ArrowoidFunc (FaustCastOp _)))
  = PureNode 1 (case (t1,t2) of
                   ([FaustFloat],[FaustInt]) -> \x -> let [FaustDataFloat f] = x in [FaustDataInt (round f)]
                   ([FaustInt],[FaustFloat]) -> \x -> let [FaustDataInt f] = x in [FaustDataFloat (fromIntegral f)]
                   otherwise -> id
               )
interpretFaustArrow (TypeTag _ _ (ArrowoidFunc (FaustGen _ d))) = PureNode 0 (const [d])
interpretFaustArrow (TypeTag _ _ (ArrowoidFunc (FaustRdtable _ arr))) = PureNode 1 (return . (arr !) . getInt . head)
interpretFaustArrow (TypeTag i _ (ArrowoidId)) = PureNode (length i) id
interpretFaustArrow (TypeTag _ _ (ArrowoidCompose a b)) = (interpretFaustArrow a) >>> (interpretFaustArrow b)
interpretFaustArrow (TypeTag _ _ (ArrowoidSplit a b)) = (interpretFaustArrow a) *** (interpretFaustArrow b)

renderArrowReversed :: RuntimeFaustArrow -> [[FaustData]] -> (RuntimeFaustArrow,[[FaustData]])
renderArrowReversed arr (x:xs) = let (parr,pd) = renderArrowReversed arr xs in
                                   let (narr,nd) = runArrow parr x in
                                     (narr,nd:pd)
renderArrowReversed arr _ = (arr,[])
renderArrow arr l = let (narr,o) = renderArrowReversed arr (reverse l) in (narr,reverse o)


ptestArr =  (ArrowCompose (ArrowCompose (ArrowSplit (ArrowCompose (ArrowSplit ArrowId ArrowId) (ArrowFunc (FaustIntFloatOp FaustDiv))) (ArrowFunc (FaustGen FaustInt (FaustDataInt 8)))) (ArrowFunc (FaustIntBinOp FaustMod))) (ArrowFunc (FaustRdtable FaustFloat (listArray (0,7) (map FaustDataFloat $ [0.0,0.5,1.0,0.5,0.0,-0.5,-1.0,-0.5])))))
testArr = (ArrowCompose (ArrowSplit (ArrowCompose (ArrowSplit ptestArr ptestArr) (ArrowFunc (FaustIntFloatOp FaustAdd))) (ArrowFunc (FaustGen FaustFloat (FaustDataFloat 0.5)))) (ArrowFunc (FaustIntFloatOp FaustMul)))
[MultipleMonadError [] (Just p)] = typeFaustArrow testArr
pt = interpretFaustArrow p
main = do
  let samples = map (map (doubleToSample.float2Double.getFloat))
                        (snd (renderArrow pt
                              (map (\(x,y,z,w) -> [FaustDataInt x,FaustDataInt y,FaustDataInt z,FaustDataInt w]) $
                               (zip4 [0,1 .. 88200] ((replicate 44100 75)
                                                   ++(replicate 44101 60))
                                 [0,1 .. 88200] ((replicate 44100 50)
                                                  ++(replicate 44101 40))
                               ))))
  let wav = WAVE {
    waveHeader = WAVEHeader {
      waveNumChannels = 1,
      waveFrameRate = 44100,
      waveBitsPerSample = 16,
      waveFrames = Nothing },
    waveSamples = samples }
  putWAVEFile "test.wav" wav
