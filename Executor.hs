{-# LANGUAGE PatternGuards, ViewPatterns #-}
module Executor where

import qualified Data.Array.Unboxed as U
import Array (Array, Ix)
import Data.Array.IArray ((!), (//))
import Word (Word16)

data GD = GD (Array Side PD) deriving Show -- FIXME: they really should be consistent

unGD (GD v) = v

data Side = ME | OP deriving (Eq, Ord, Ix, Show)

other ME = OP
other OP = ME

data PD = PD {pd_vit :: U.Array Int Word16, pd_alive :: U.Array Int Bool, pd_field :: Array Int Func } deriving Show

data Card = I | F_zero | F_succ | F_dbl | F_get | F_put | S | K | F_inc | F_dec | F_attack | F_help | F_copy | F_revive | F_zombie
  deriving (Eq, Ord, Ix, Show)

ccode I = "I"
ccode F_zero = "zero"
ccode F_succ = "succ"
ccode F_dbl = "dbl"
ccode F_get = "get"
ccode F_put = "put"
ccode S = "S"
ccode K = "K"
ccode F_inc = "inc"
ccode F_dec = "dec"
ccode F_attack = "attack"
ccode F_help = "help"
ccode F_copy = "copy"
ccode F_revive = "revive"
ccode F_zombie = "zombie"

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

data Func =
  Value Word16
  | Card Card
  | Partial Card [Func] -- Int means how many left to full call
  deriving Show

-- TODO: optimize it with adding diffs; cannot tolerate seeing how it rips arrays
-- FIXME: err must throw!
apply gd side count0 func arg =
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
    -- FIXME: change x to 255-x where needed
    expand I [x] = (gd, count, Just x)
    expand F_succ [Value 65535] = (gd, count, Just $ Value 65535)
    expand F_succ [Value x] = (gd, count, Just $ Value $ x + 1)
    expand F_succ [_] = err
    expand F_dbl [Value n] | n < 32768 = (gd, count, Just $ Value $ 2 * n)
    expand F_dbl [Value n] = (gd, count, Just $ Value 65535)
    expand F_dbl [_] = err
    expand F_get [iv] | Just i <- castIx iv
                                  , pd_alive pd ! i
                                  = (gd, count, Just $ Value $ pd_vit pd ! i)
    expand F_get [_] = err
    expand F_put [_] = (gd, count, Just $ Card I) -- not error!
    expand S [x, g, f] =
      case apply gd side count f x of
        (gd'', count'', Nothing) -> (gd'', count'', Nothing)
        (gd'', count'', Just h) ->
          case apply gd'' side count'' g x of
            (gd''', count''', Nothing) -> (gd''', count''', Nothing)
            (gd''', count''', Just y) -> apply gd''' side count''' h y
    expand K [y, x] = (gd, count, Just x)
    expand F_inc [iv] | Just i <- castIx iv =
      let
        gd' = if pd_alive pd ! i
                then
                  let
                    v = pd_vit pd ! i
                  in if v == 65535 then gd else GD (gdV // [(side, pd {pd_vit = pd_vit pd // [(i, v + 1)]})])
                else gd
      in (gd', count, Just $ Card I)
    expand F_inc [_] = err
    expand F_dec [castIx -> Just i] =
      let
        gd' = if pd_alive pd ! i
                then
                    if v == 1
                      then GD (gdV // [(side, pd {pd_alive = pd_alive pd // [(i, False)]})])
                      else GD (gdV // [(side, pd {pd_vit = pd_vit pd // [(i, v - 1)]})])
                else gd
        v = pd_vit pd ! i
      in (gd', count, Just $ Card I)
    expand F_dec [_] = err
    expand F_help [Value n, castIx -> Just j, castIx -> Just i] = (gd', count, Just $ Card I)
      where
        gd' = if pd_alive od ! i
                then GD (gdV // [(other side, od {pd_vit = pd_vit od // [(i, v')]})])
                else gd
        v = pd_vit od ! i
        v' = fromInteger $ min 65535 (toInteger n * 11 `div` 10 + toInteger v)
    expand F_help [_, _, _] = err
    expand F_attack [Value n, castIx -> Just j, castIx -> Just i] = (gd', count, Just $ Card I)
      where
        gd' = if pd_alive od ! i && v' > 0
                then if v' > 0
                  then GD (gdV // [(other side, od {pd_vit = pd_vit od // [(i, v')]})])
                  else GD (gdV // [(other side, od {pd_alive = pd_alive od // [(i, False)]})])
                else gd
        v = pd_vit od ! i
        v' = fromInteger $ max 0 (toInteger v - toInteger n * 9 `div` 10)
    expand F_attack [_, _, _] = err
    expand F_copy [castIx -> Just i] = (gd, count, Just (pd_field od ! i))
    expand F_copy [_] = err
    expand F_revive [castIx -> Just i] = (gd', count, Just $ Card I)
      where
        gd' = if pd_alive pd ! i
                then gd
                else GD (gdV // [(side, pd {pd_alive = pd_alive pd // [(i, True)]
                                            , pd_vit = pd_vit pd // [(i, 1)]})])
    expand F_revive [_] = err
    expand F_zombie [Value x, castIx -> Just i] | not (pd_alive od ! i) = (gd', count, Just $ Card I)
      where
        gd' = GD (gdV // [(other side, od {pd_alive = pd_alive od // [(i, True)]
                                          , pd_vit = pd_vit od // [(i, x)]})])
    expand F_zombie [_] = err
    (GD gdV) = gd
    pd = gdV ! side
    od = gdV ! (other side)
    err = (gd, count, Nothing)
    count = count0 + 1
