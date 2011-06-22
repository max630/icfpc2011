{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE PatternGuards, ViewPatterns, GADTs, EmptyDataDecls #-}
module Main where

import Prelude hiding (succ)
import Word (Word16)
import System (getArgs)
import System.IO (hFlush)
import IO (stdout)
import List (intersperse)
import Random (randomRIO)
import Control.Concurrent (threadDelay)
import Data.IORef (newIORef, readIORef, writeIORef)
import System.IO.Unsafe (unsafePerformIO)

data Card = I | F_zero | F_succ | F_dbl | F_get | F_put | S | K | F_inc | F_dec | F_attack | F_help | F_copy | F_revive | F_zombie
  deriving (Eq, Ord, Show)

pprC I = "I"
pprC F_zero = "zero"
pprC F_succ = "succ"
pprC F_dbl = "dbl"
pprC F_get = "get"
pprC F_put = "put"
pprC S = "S"
pprC K = "K"
pprC F_inc = "inc"
pprC F_dec = "dec"
pprC F_attack = "attack"
pprC F_help = "help"
pprC F_copy = "copy"
pprC F_revive = "revive"
pprC F_zombie = "zombie"

readC "I" = I
readC "zero" = F_zero
readC "succ" = F_succ
readC "dbl" = F_dbl
readC "get" = F_get
readC "put" = F_put
readC "S" = S
readC "K" = K
readC "inc" = F_inc
readC "dec" = F_dec
readC "attack" = F_attack
readC "help" = F_help
readC "copy" = F_copy
readC "revive" = F_revive
readC "zombie" = F_zombie
readC s = error ("Bad card: " ++ s)

arity I = 1
arity F_zero = 0
arity F_succ = 1
arity F_dbl = 1
arity F_get = 1
arity F_put = 1
arity S = 3
arity K = 2
arity F_inc = 1
arity F_dec = 1
arity F_attack = 3
arity F_help = 3
arity F_copy = 1
arity F_revive = 1
arity F_zombie = 2

returnsIC F_put = True
returnsIC F_inc = True
returnsIC F_dec = True
returnsIC F_attack = True
returnsIC F_help = True
returnsIC F_copy = True
returnsIC F_revive = True
returnsIC F_zombie = True
returnsIC _ = False

-- nice optimization
returnsI :: Func a -> Bool
returnsI (Lazy _ f) = returnsI f
returnsI (Value _) = False
returnsI (Var _) = False -- this can be true but please dont make me implement full-size typecheck
returnsI (Apply (Lambda _ f) _) = returnsI f
returnsI (getCall -> (Card c : fs)) = returnsIC c && arity c == length fs
returnsI (Apply _ _) = False -- this also can be true
returnsI (Seq _ f) = returnsI f
returnsI (Card _) = False
returnsI (Lambda _ _) = False

castIx (Value n) | n >= 0 && n <= 255 = Just $ fromInteger (toInteger n)
castIx _ = Nothing

data FSrc = FSrc
data FComb = FComb

data Func a where
  Value :: Word16 -> Func a
  Card :: Card -> Func a
  -- Partial :: Card -> [Func a] -> Func a
  Apply :: Func a -> Func a -> Func a
  Lambda :: String -> Func FSrc -> Func FSrc
  Var :: String -> Func FSrc
  Lazy :: String -> Func FSrc -> Func FSrc
  Seq :: Func FSrc -> Func FSrc -> Func FSrc

castComb :: Func a -> Func FComb
castComb (Value v) = Value v
castComb (Card c) = Card c
castComb (Apply f1 f2) = Apply (castComb f1) (castComb f2)
castComb f = error ("Not transformed:" ++ pprF f)


instance Show (Func a) where
  show = pprF

call [] = error "Empty call!"
call [f] = f
call fs = Apply (call $ init fs) (last fs)

getCall (Apply f1 f2) = getCall f1 ++ [f2]
getCall f = [f]

getSeq :: Func FSrc -> [Func FSrc]
getSeq (Seq f1 f2) = getSeq f1 ++ getSeq f2
getSeq f = [f]

pprF :: Func a -> String
pprF (Value n) = show n
pprF (Card c) = pprC c
pprF f@(Apply f1 f2) = concat $ intersperse " " $ map pprarg (getCall f)
  where
    pprarg a@(Apply _ _) = "(" ++ pprF a ++ ")"
    pprarg a = pprF a
pprF (Lambda s f) = "(\\ " ++ s ++ " -> " ++ pprF f ++ ")"
pprF (Var s) = s
pprF (Lazy s f) = "((lazy " ++ s ++ ") " ++ pprF f ++ ")"
pprF f@(Seq f1 f2) = "[" ++ concat (intersperse ", " (map pprF (getSeq f))) ++ "]"

data Step = Move | Clean deriving (Eq, Ord, Show)

-- requirements for "stacked" form:
-- stacked (Card _)
-- stacked (Partial c (Card _ : fs)) && stacked (Partial c fs)
-- stacked (Partial _ [f]) && stacked f

stack :: Func FComb -> Func FComb
stack (Value 0) = Card F_zero
stack (Value n) = if n `mod` 2 == 0
                    then Apply (Card F_dbl) (stack (Value (n `div` 2)))
                    else Apply (Card F_succ) (stack (Value (n - 1)))
stack e@(Card _) = e
stack (Apply (Card c) f) = Apply (Card c) (stack f)
stack (Apply f (Card c)) = Apply (stack f) (Card c)
stack (Apply f1 f2@(Value v)) = stack (Apply f1 (stack f2))
stack (Apply f1 (Apply f2 f3)) = stack (call [Card S, Apply (Card K) f1, f2, f3])

generator f = reverse $ gen (stack f)
  where
    gen (Card c) = [Right c]
    gen (Apply f (Card c)) = (Right c : gen f)
    gen (Apply (Card c) f) = (Left c : gen f)
    gen f = error ("unexpected stacked function: " ++ pprF f)

attack fs = call (Card F_attack : fs)
s fs = call (Card S : fs)
k fs = call (Card K : fs)
succ fs = call (Card F_succ : fs)
succV = Card F_succ
zero = Card F_zero
getV = Card F_get
get fs = call (Card F_get : fs)

killallA3 pos = Lambda "n" (call [Card F_help, Var "n", Value 0, Value 9984]
                        `Seq` attack [Value 0, Var "n", Value 11264]
                        `Seq` Apply (Lazy "n" (get [Value pos])) (succ [Var "n"]))


-- TODO: why I cannot put a here? report this issue to ghc
closure :: Func FSrc -> Maybe (Func FSrc, Func FSrc)
closure (Apply f1 f2) = Just (f1, f2)
closure _ = Nothing

transformX :: Func FSrc -> Func FSrc
transformX (Value v) = Value v
transformX (Card c) = Card c
transformX (Apply f1 f2) = Apply (transformX f1) (transformX f2)
transformX (Lazy v f) = Lazy v f
transformX (Var v) = Var v
transformX f@(Seq _ _) = error ("sequence outside of lambda:" ++ pprF f)
transformX (Lambda v f) | not (contains v f) = k [transformX f]
transformX (Lambda v (Apply (Lazy v1 (Apply f1 f2)) (Var v2))) | v == v1 && v1 == v2 = s [transformX (Lambda v f1), transformX (Lambda v f2)]
transformX (Lambda v (closure -> Just (head, Var v1))) | v == v1 && not (contains v head) = transformX head
transformX f0@(Lambda v (closure -> Just (head, f))) =
  --seq
  --  (unsafePerformIO (putStrLn $ "l:" ++ show f0))
    (s [transformX (Lambda v head), transformX (Lambda v f)])
transformX f0@(Lambda v (Lazy v1 (closure -> Just (head, f)))) | v == v1 =
  --seq
  --  (unsafePerformIO (putStrLn $ "l2:" ++ show f0))
    (s [transformX (Lambda v head), transformX (Lambda v f)])
transformX (Lambda v (Seq f1 f2)) | returnsI f1 =
  s [ transformX (Lambda v f1), transformX (Lambda v f2) ]
-- transformX (Lambda v (Seq f1 f2)) =
--   s [transformX (Lambda v (s [k [f2], k [Var v]])), transformX (Lambda v f1)]
transformX (Lambda v1 f1@(Lambda v2 _)) | v1 /= v2 = transformX (Lambda v1 (transformX f1))
transformX (Lambda v (Var v1)) | v == v1 = Card I
transformX (Lambda v f) = error ("Cannot transformX: " ++ pprF f ++ ", var " ++ v)

transform f = castComb $ transformX f

contains :: String -> Func a -> Bool
contains v f0 = case f0 of
    Card _ -> False
    Value _ -> False
    Var v1 -> v == v1
    Apply f1 f2 -> contains v f1 || contains v f2
    Lambda v1 _ | v1 == v -> error ("shadowed variable: " ++ v)
    Lambda v1 f -> contains v f
    Lazy v1 f -> v == v1 || contains v f
    Seq f1 f2 -> contains v f1 || contains v f2

pMove slot cmd =
  case cmd of
    Left c -> do
              print 1
              putStrLn $ pprC c
              print slot
    Right c -> do
              print 2
              print slot
              putStrLn $ pprC c

-- TODO: correct output types
oMove =
  do
    mode <- getLine
    if mode == "1"
      then do
        card <- getLine
        slotS <- getLine
        return (read slotS, Left $ readC card)
      else do
        slotS <- getLine
        card <- getLine
        return (read slotS :: Int, Right $ readC card)

interaction f =
  do
    [a0] <- getArgs
    if a0 == "1"
      then oMove >>= \ d -> loop (Just d)
      else loop Nothing
  where
    loop o =
      do
        (slot, cmd) <- f o
        pMove slot cmd
        hFlush stdout
        newO <- oMove
        loop (Just newO)

dumpF commands pos =
  do
    cmds <- readIORef commands
    case cmds of
      (cmd : rest) ->
        do
          writeIORef commands rest
          return cmd
      _ -> return (0, Left I)

callCmds pos = concat (map (callOnce pos) [(pos + 1), (pos + 49) .. 255] ++ map (callOnce pos) [0, 49 .. pos])

callOnce pos arg = zip (repeat arg) (generator (stack (transform (callOnceCmd pos arg))))

callOnceCmd pos arg = call [Card F_get, Value pos, Value arg]

main =
  do
    posI <- randomRIO (0, 255)
    let
      pos = fromInteger posI
      setup = zip (repeat pos) (generator $ stack $ transform (killallA3 pos))
      calls = callCmds pos
    commands <- newIORef (setup ++ calls)
    interaction $ (\ _ -> dumpF commands pos)

