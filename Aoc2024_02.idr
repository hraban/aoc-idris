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

-- Like alldec, but automatically detect if the list is consistently increasing
-- or decreasing
allsame : List Int -> Bool
allsame [] = True
allsame [ _ ] = True
allsame (x :: (y :: rest)) = False -- TODO

-- How express "at least two elements"?
data Order = Increasing | Decreasing | Mixed

compare2 : Int -> Int -> Order
compare2 x y =
  if (x > y) then Decreasing
  else if (x < y) then Increasing
  else Mixed -- We only care about strict order

allsame' : { n : Nat } -> { auto prf: n > 1 = True } -> Vect n Int -> Order
allsame' [ x, y ] =
  compare2 x y
allsame' (x :: (y :: rest)) =
  case compare2 x y of
    Mixed => Mixed
    Increasing => case allsame' (y :: rest) of
                    Increasing => Increasing
                    _ => Mixed
    Decreasing => case allsame' (y :: rest) of
                    Decreasing => Decreasing
                    _ => Mixed



-- detlvls : List Number -> Bool
-- detlvls [] = True
-- detlvls [ _ ] = True
-- detlvls (x :: y :: rest) = True
