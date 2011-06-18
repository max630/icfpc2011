{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE PatternGuards, ViewPatterns, GADTs, EmptyDataDecls #-}
module Main where

import qualified Data.Array.Unboxed as U
import Array (Array, Ix)
import Data.Array.IArray ((!), (//))
import Word (Word16)
import System (getArgs)
import System.IO (hFlush)
import IO (stdout)
import Control.Concurrent (threadDelay)

data GD = GD (Array Side PD) deriving Show -- FIXME: they really should be consistent

unGD (GD v) = v

data Side = ME | OP deriving (Eq, Ord, Ix, Show)

other ME = OP
other OP = ME

data PD = PD {pd_vit :: U.Array Int Int, pd_field :: Array Int (Func FComb) } deriving Show

data Card = I | F_zero | F_succ | F_dbl | F_get | F_put | S | K | F_inc | F_dec | F_attack | F_help | F_copy | F_revive | F_zombie
  deriving (Eq, Ord, Ix, Show)

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

castIx (Value n) | n >= 0 && n <= 255 = Just $ fromInteger (toInteger n)
castIx _ = Nothing

{- data Func =
  Value Word16
  | Card Card
  | Partial Card [Func] -- Int means how many left to full call
  deriving Show -}

data FSrc
data FComb

data Func a where
  Value :: Word16 -> Func a
  Card :: Card -> Func a
  Partial :: Card -> [Func a] -> Func a
  Lambda :: String -> Func FSrc -> Func FSrc
  Var :: String -> Func FSrc
  Lazy :: String -> Func FSrc -> Func FSrc
  Seq :: Func FSrc -> Func FSrc -> Func FSrc

instance Show (Func a) where
  show = pprF

pprF :: Func a -> String
pprF (Value n) = show n
pprF (Card c) = pprC c
pprF (Partial c fs) = pprC c ++ (concat $ map pprarg $ reverse fs)
  where
    pprarg a@(Partial _ _) = " (" ++ pprF a ++ ")"
    pprarg a = " " ++ pprF a
pprF (Lambda s f) = "(\\ " ++ s ++ " -> " ++ pprF f ++ ")"
pprF (Var s) = s
pprF (Lazy s f) = "((lazy " ++ s ++ ") " ++ pprF f ++ ")"
pprF (Seq f1 f2) = "[" ++ pprF f1 ++ ", " ++ pprF f2 ++ "]"

data Step = Move | Clean deriving (Eq, Ord, Show)

-- TODO: optimize it with adding diffs; cannot tolerate seeing how it rips arrays
-- FIXME: err must throw!
apply step gd side count0 func arg =
  if count0 >= 1000
    then err
    else
      case func of
        Value _ -> err
        Card c -> case arity c of
          0 -> err
          1 -> expand c [arg]
          _ -> (gd, count, Just $ Partial c [arg])
        Partial c pargs ->
          if arity c > length pargs + 1
            then (gd, count, Just $ Partial c (arg : pargs))
            else expand c (arg : pargs)
  where
    expand I [x] = (gd, count, Just x)
    expand F_succ [Value 65535] = (gd, count, Just $ Value 65535)
    expand F_succ [Value x] = (gd, count, Just $ Value $ x + 1)
    expand F_succ [_] = err
    expand F_dbl [Value n] | n < 32768 = (gd, count, Just $ Value $ 2 * n)
    expand F_dbl [Value n] = (gd, count, Just $ Value 65535)
    expand F_dbl [_] = err
    expand F_get [castIx -> Just i] | pd_vit pd ! i > 0 = (gd, count, Just $ Value $ fromInteger $ toInteger (pd_vit pd ! i))
    expand F_get [_] = err
    expand F_put [_] = (gd, count, Just $ Card I) -- not error!
    expand S [x, g, f] =
      case apply step gd side count f x of
        (gd'', count'', Nothing) -> (gd'', count'', Nothing)
        (gd'', count'', Just h) ->
          case apply step gd'' side count'' g x of
            (gd''', count''', Nothing) -> (gd''', count''', Nothing)
            (gd''', count''', Just y) -> apply step gd''' side count''' h y
    expand K [y, x] = (gd, count, Just x)
    expand F_inc [castIx -> Just i] = (gd', count, Just $ Card I)
      where
        gd' = case step of
                Move | v > 0 && v < 65535
                      -> GD (gdV // [(side, pd {pd_vit = pd_vit pd // [(i, v + 1)]})])
                Clean | v > 0
                      -> GD (gdV // [(side, pd {pd_vit = pd_vit pd // [(i, v - 1)]})])
                _ -> gd
        v = pd_vit pd ! i
    expand F_inc [_] = err
    expand F_dec [castIx -> Just i0] = (gd', count, Just $ Card I)
      where 
        gd' = case step of
                Move | v > 0
                     -> GD (gdV // [(side, od {pd_vit = pd_vit od // [(i1, v - 1)]})])
                Clean | v > 0 && v < 65535
                     -> GD (gdV // [(side, od {pd_vit = pd_vit od // [(i1, v + 1)]})])
                _ -> gd
        v = pd_vit od ! i1
        i1 = 255 - i0
    expand F_dec [_] = err
    expand F_help [Value n, castIx -> Just j, castIx -> Just i] = (gd', count, Just $ Card I)
      where
        gd' = case step of
                Move | v > 0
                    -> GD (gdV // [(other side, pd {pd_vit = pd_vit pd // [(i, v')]})])
                Clean | v > 0
                    -> GD (gdV // [(other side, pd {pd_vit = pd_vit pd // [(i, v'')]})])
                _ -> gd
        v = pd_vit pd ! i
        v' = fromInteger $ min 65535 (toInteger v + toInteger n * 11 `div` 10)
        v'' = fromInteger $ max 0 (toInteger v - toInteger n * 11 `div` 10)
    expand F_help [_, _, _] = err
    expand F_attack [Value n, castIx -> Just j, castIx -> Just i0] = (gd', count, Just $ Card I)
      where
        gd' = case step of
                Move | v > 0
                     -> GD (gdV // [(other side, od {pd_vit = pd_vit od // [(i1, v')]})])
                Clean | v > 0
                     -> GD (gdV // [(other side, od {pd_vit = pd_vit od // [(i1, v'')]})])
                _ -> gd
        v = pd_vit od ! i1
        v' = fromInteger $ max 0 (toInteger v - toInteger n * 9 `div` 10)
        v'' = fromInteger $ min 65535 (toInteger v + toInteger n * 9 `div` 10)
        i1 = 255 - i0
    expand F_attack [_, _, _] = err
    expand F_copy [castIx -> Just i] = (gd, count, Just (pd_field od ! i))
    expand F_copy [_] = err
    expand F_revive [castIx -> Just i] = (gd', count, Just $ Card I)
      where
        gd' = if pd_vit pd ! i > 0
                then gd
                else GD (gdV // [(side, pd {pd_vit = pd_vit pd // [(i, 1)]})])
    expand F_revive [_] = err
    expand F_zombie [x, castIx -> Just i0] | pd_vit od ! i1 <= 0 = (gd', count, Just $ Card I)
      where
        gd' = GD (gdV // [(other side, od {pd_vit = pd_vit od // [(i1, -1)]
                                          , pd_field = pd_field od // [(i1, x)]})])
        i1 = 255 - i0
    expand F_zombie [_] = err
    expand c args = error ("Bad expand:" ++ pprC c ++ " " ++ show args)
    (GD gdV) = gd
    pd = gdV ! side
    od = gdV ! (other side)
    err = (gd, count, Nothing)
    count = count0 + 1

-- requirements for "stacked" form:
-- stacked (Card _)
-- stacked (Partial c (Card _ : fs)) && stacked (Partial c fs)
-- stacked (Partial _ [f]) && stacked f

stack :: Func FComb -> Func FComb
stack (Value 0) = Card F_zero
stack (Value 1) = Partial F_succ [Card F_zero]
stack (Value _) = error "TODO: higher ints"
stack e@(Card _) = e
stack (Partial c []) = error "partial with zero args!"
stack (Partial c [f]) = Partial c [stack f]
stack (Partial c (f : fs)) =
  case stack f of
    Card c' -> case stack (Partial c fs) of
                Partial c fs' -> Partial c (Card c' : fs')
                _ -> error "unexpected stacked form"
    Partial c' [f'] -> stack (Partial S [f', Card c', Partial K [Partial c fs]])
    Partial c' (f' : fs') -> stack (Partial S [f', Partial c' fs', Partial K [Partial c fs]])
    f -> error ("Bad stacked: " ++ pprF f)

generator f = reverse $ gen (stack f)
  where
    gen (Card c) = [Right c]
    gen (Partial c [f]) = (Left c : gen f)
    gen (Partial c (Card c' : fs)) = (Right c' : gen (Partial c fs))
    gen _ = error "unexpected stacked function"

attack fs = Partial F_attack $ reverse fs
s fs = Partial S $ reverse fs
k fs = Partial K $ reverse fs
succ fs = Partial F_succ $ reverse fs
succV = Card F_zero
zero = Card F_zero
getV = Card F_get
get fs = Partial F_get $ reverse fs

-- FIXME: this looks to be broken; implement a languade with lambdas and fix
killall0 = (s [Card F_succ, s [s [k [Card F_zero], k [Card F_get]], s [k [Partial F_succ [Card F_zero ]], attack [Card F_zero]]]])
killallM = s [s[s[attack [(Value 0)], k[Value 1]],s[k[getV], k[zero]]], succV]

-- data Lang = Lambda String Lang | Var String | Func (Func FSrc) | Lazy String Lang

-- TODO: why I cannot put a here? report this issue to ghc
closure :: Func FSrc -> Maybe (Func FSrc, Func FSrc)
closure (Partial c [f]) = Just (Card c, f)
closure (Partial c (f : fs@(_ : _))) = Just (Partial c fs, f)
closure _ = Nothing

transform :: Func a -> Func FComb
transform (Value v) = Value v
transform (Card c) = Card c
transform (Partial c fs) = Partial c (map transform fs)
transform (Lazy v _) = error ("Unbounded variable: " ++ v)
transform (Var v) = error ("Unbounded variable:" ++ v)
transform f@(Seq _ _) = error ("sequence outside of lambda:" ++ pprF f)
transform (Lambda v f) | not (contains v f) = k [transform f]
transform (Lambda v (closure -> Just (head, Var v1))) | v == v1 && not (contains v head) = transform head
transform (Lambda v (closure -> Just (head, f))) = s [transform (Lambda v head), transform (Lambda v f)]
transform (Lambda v (Lazy v1 (closure -> Just (head, f)))) | v == v1
                                                = s [transform (Lambda v head), transform (Lambda v f)]
transform (Lambda v (Seq f1 f2)) =
  transform $
    s [ Lambda v (s [k [f2], k [Var v]])
        , Lambda v f1
      ]
transform (Lambda v f) = error ("Cannot transform: " ++ pprF f ++ ", var " ++ v)
-- transform (Lambda v (Var v1)) | v == v1 = Card I

contains :: String -> Func a -> Bool
contains v f = case f of
    Card _ -> False
    Value _ -> False
    Var v1 -> v == v1
    Partial c fs -> or (map (contains v) fs)
    Lambda v1 _ | v1 == v -> error ("shadowed variable: " ++ v)
    Lambda v1 f -> contains v f
    Lazy v1 f -> v == v1 || contains v f
    Seq f1 f2 -> contains v f1 || contains v f2

-- main' = putStrLn $ concat $ map (\s -> case s of { Right x -> "2\n0\n" ++ pprC x ++ "\n"; Left x -> "1\n" ++ pprC x ++ "\n0\n" }) $ generator killall

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
        threadDelay 1000000
        loop (Just newO)

main = interaction (\ _ -> return (0, Left I) )
