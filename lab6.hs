-- Lab 6: FSM constructions for regular operators
-- Mark Philipp
-- 109941708

import Data.List (nub, sort, subsequences)


-- Fixed alphabet, but everything below should work for any sigma!
sigma = "ab"

-- Finite state machines indexed by the type of their states
-- M = (states, start, final, transitions)
type FSM a = ([a], a, [a], [(a, Char, a)])


---------------- A solution to Lab 5, ported to FSM a ------------------------
  
-- no_dups xs = "xs has no duplicates"
no_dups :: Eq a => [a] -> Bool
no_dups [] = True
no_dups (x:xs) = not (elem x xs) && no_dups xs

-- subset xs ys == "xs is a subset of ys"
subset :: Eq a => [a] -> [a] -> Bool
subset [] ys = True
subset (x:xs) ys = elem x ys && subset xs ys

-- func3 as bs ts == "ts determines a function from (as x bs) to cs"
func3 :: (Eq a, Eq b, Eq c) => [a] -> [b] -> [c] -> [(a,b,c)] -> Bool
func3 as bs cs ts = and [single (thirds a b ts) cs | a <- as, b <- bs] where
  thirds a b ts = [c' | (a',b',c') <- ts, a' == a, b' == b]
  single [x] ys = elem x ys
  single _ _ = False

-- check whether a finite state machine is correct/complete:
checkFSM :: Eq a => FSM a -> Bool
checkFSM (qs, s, fs, d) = no_dups qs &&        -- (1)
                          elem s qs &&         -- (2)
                          subset fs qs &&      -- (3)
                          func3 qs sigma qs d  -- (4)

-- All functions below assume that the machine is correct

-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a

delta :: Eq a => FSM a -> a -> Char -> a
delta (_, _, _, d) = ap d

delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star = foldl . delta

accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m@(qs, q0, fs, d) w = elem (delta_star m q0 w) fs

accept2_aux :: Eq a => FSM a -> a -> [Char] -> Bool
accept2_aux m@(_, _, fs, _) q [] = elem q fs
accept2_aux m q (a:w) = accept2_aux m (delta m q a) w

accept2 :: Eq a => FSM a -> [Char] -> Bool
accept2 m@(_, q0, _, _) w = accept2_aux m q0 w

-- even_as is a machine that accepts strings with an even number of a's
-- states: (number of a's read so far) mod 2
even_as :: FSM Int
even_as = ([0,1], 0, [0], [(i, a, d i a) | i <- [0,1], a <- sigma]) where
  d i 'a' = (i + 1) `mod` 2
  d i 'b' = i

-- no_aaa is a machine that accepts strings that don't have three a's in a row
-- states: number of a's in a row just read (n = 0, 1, 2), 3 is a trap
no_aaa :: FSM Int
no_aaa = ([0..3], 0, [0..2], [(i, a, d i a) | i <- [0..3], a <- sigma]) where
  d i 'a' = min 3 (i + 1)
  d 3 'b' = 3
  d _ 'b' = 0


---------------- Some additional useful functions --------------------------

-- Normalize a list, i.e., sort and remove (now adjacent) duplicates.
-- Two lists determine the same set if they normalize to the same list
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys

-- Cartesian product
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys


---------------- Lab 6 begins here -----------------------------------------

-- Complete the FSM constructions for the 6 language constructs and test your
-- functions adequately
-- ex1 :: FSM Int
-- ex1 = ([0], 0, [0], [()])

-- ex2 :: FSM Char
-- ex2 = ("ab", 'a', "a", [("ab", 'a', "bc")])

-- (norm "bab") == (norm "ab") will return true. Gets rid of duplicate elements of string set

-- use reachable when outputting test results

-- Machine that accepts the empty language
emptyFSM :: FSM Int
emptyFSM = ([0, 1], 0, [0], [(x, letter, 1) | x <- [0, 1], letter <- sigma])

-- Machine that accepts the language {"a"} where a in sigma
letterFSM :: Char -> FSM Int
letterFSM a = ([0, 1, 2], 0, [1], [(x, letter, final) | x <- [0, 1, 2], letter <- sigma, let final = if x == 0 && letter == a then 1 else 2])

-- Machine that accepts the language {w} where w in sigma*
stringFSM :: [Char] -> FSM Int
-- (length w) + 1 should be our trap state. (length w ) should be our final state for the accepted string.
stringFSM w = ([0..(length w) + 1], 0, [(length w)], [(x, letter, final) | x <- [0..(length w) + 1], letter <- sigma, let final = if x < (length w) && letter == (w !! x) then x + 1 else (length w) + 1])

-- Machine that accepts the union of the languages accepted by m1 and m2
unionFSM :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a, b)
unionFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1, s2)
  fs = [(q1, q2) | q1 <- fs1, q2 <- fs2, overlap (fs1 >< qs2) (qs1 >< fs2) == False]
  d  = undefined

-- Machine that accepts the concatenation of the languages accepted by m1 and m2
catFSM :: (Eq a, Ord b) => FSM a -> FSM b -> FSM (a, [b])
catFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = undefined
  s  = undefined
  fs = undefined
  d  = undefined

-- Machine that accepts the Kleene star of the language accepted by m1
starFSM :: Ord a => FSM a -> FSM [a]
starFSM (qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = undefined
  s  = undefined
  fs = undefined
  d  = undefined

  
  
-- Bonus Feature (for testing):

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable m@(qs, q0, fs, d) = (qs', q0, fs', d') where
  qs' = sort $ stable $ iterate close ([q0], [])
  fs' = filter (`elem` qs') fs
  d'  = filter (\(q,_,_) -> q `elem` qs') d
  stable ((fr,qs):rest) = if null fr then qs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = nub $ filter (`notElem` xs') (concatMap step fr)
    step q = map (ap d q) sigma
