-- Copyright © 2024  Hraban Luyat & Fée Elders
--
-- Licensed under the AGPL, v3 only. See LICENSE file.

-- sandbox for aoc 2024 day 2

module Aoc2024_02

import Data.String
import Data.Vect
import System.File

main : IO ()
main = putStrLn "Hello world"


greet : IO ()
greet = do putStr "What is your name? "
           name <- getLine
           putStrLn ("Hello " ++ name)

-- ???
-- sum : IO () => (state : a) ->
iosum : IO ()
iosum = do eof <- fEOF stdin
           if eof
             then pure ()
             else do x <- getLine
                     case parsePositive x of
                          Just (n) =>
                            putStrLn ("> " ++ (show (n * n)))
                          Nothing =>
                            putStrLn ("NaN: " ++ x)
                     iosum


-- Is every element in this list strictly lower than its predecessor?
total
alldec : List Int -> Bool
alldec [] = True
alldec [ _ ] = True
alldec (x :: (y :: rest)) =
  case x > y of
    False => False
    True => alldec (y :: rest)

-- Is this how idris works?
-- sortInc : List Int -> IncreasingList Int
-- sortDec : List Int -> DecreasingList Int
-- data OrderedList a = (?? has(>, a) ??) IncreasingList a | DecreasingList a
-- data Order = Increasing | Decreasing
-- sort : (order: Order) -> List Int -> if order == Increasing then IncreasingList Int else DecreasingList Int
-- sort order list = ...

-- This is pointless in the face of Order but it’s educational
data Order = Increasing | Decreasing | Mixed
Eq Order where
  Increasing == Increasing = True
  Decreasing == Decreasing = True
  Mixed == Mixed = True
  _ == _ = False

total
compare2 : Int -> Int -> Order
compare2 x y = case compare x y of
                 LT => Increasing
                 GT => Decreasing
                 _  => Mixed

record VectMinLen (n : Nat) (a : Type) where
  constructor MkVectMinLen
  size : Nat
  min : GTE size n
  vect : Vect size a

-- This function is undefined on any vector with len < 2.  Let’s see if we can
-- somehow convince Idris to help us type check that!
total
get_order : VectMinLen 2 Int -> Order
get_order (MkVectMinLen size min vect) =
  -- It feels a bit double to have to babysit the proof checker like this.
  -- Isn’t this information already contained in the Vect itself?
  case size of
    2 => let [x, y] = vect in
         compare2 x y
    _ => let (x :: (y :: rest)) = vect
             init = (y, compare2 x y)
             full = foldl {acc=Acc} f init rest in
         snd full
           where
             data Acc = Pair Int Order
             init : Acc
             full : Acc
             f : Acc -> Int -> Acc
             f (Pair prev ord) el =
               let ord' = if (compare2 prev el) == ord then ord else Mixed in
                 MkPair el ord'
                 where
                   ord' : Order

-- get_order [ x y ] = compare2 x y
-- -- Does Idris understand rest is now non-empty?
-- get_order (x :: (y :: rest)) =
--   -- TODO: there has to be a way to make this more DRY (Don’t Repeat Yourself)
--   case compare2 x y of
--     Mixed => Mixed -- no need to compare the rest
--     Increasing => case get_order (y :: rest) of
--                     Increasing => Increasing
--                     _ => Mixed
--     Decreasing => case get_order (y :: rest) of
--                     Decreasing => Decreasing
--                     _ => Mixed

-- Like alldec, but automatically detect if the list is consistently increasing
-- or decreasing
allsame : { n : Nat } -> Vect n Int -> Bool
allsame [] = True
allsame [ _ ] = True
-- How do I convince Idris that x is now a valid VectMinLen 2 Int?
allsame x = let bounded = MkVectMinLen n 2 x in
                get_order bounded /= Mixed

-- allsame' : { n : Nat } -> { auto prf: n > 1 = True } -> Vect n Int -> Order
-- allsame' [ x, y ] =
--   compare2 x y
-- allsame' (x :: (y :: rest)) =
--   case compare2 x y of
--     Mixed => Mixed
--     Increasing => case allsame' (y :: rest) of
--                     Increasing => Increasing
--                     _ => Mixed
--     Decreasing => case allsame' (y :: rest) of
--                     Decreasing => Decreasing
--                     _ => Mixed

-- SO user gallais argues against the above approach:
-- https://stackoverflow.com/a/49193935/4359699


-- detlvls : List Number -> Bool
-- detlvls [] = True
-- detlvls [ _ ] = True
-- detlvls (x :: y :: rest) = True
