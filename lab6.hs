-- Lab 6: FSM constructions for regular operators
-- Mark Philipp
-- 109941708

import Data.List (nub, sort, subsequences)


-- Fixed alphabet, but everything below should work for any sigma!
sigma = "ab"

-- Finite state machines indexed by the type of their states
-- M = (states, start, final, transitions)
type FSM a = ([a], a, [a], [(a, Char, a)])

bob :: FSM Int
bob = ([0, 1], 0, [1], [(0, 'a', 1), (1, 'a', 1), (0, 'b', 0), (1, 'b', 0)])
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

{-
*Main> emptyFSM
([0,1],0,[0],[(0,'a',1),(0,'b',1),(1,'a',1),(1,'b',1)])
-}

-- Machine that accepts the language {"a"} where a in sigma
letterFSM :: Char -> FSM Int
letterFSM a = ([0, 1, 2], 0, [1], [(x, letter, final) | x <- [0, 1, 2], letter <- sigma, let final = if x == 0 && letter == a then 1 else 2])

{-
*Main> letterFSM 'a'
([0,1,2],0,[1],[(0,'a',1),(0,'b',2),(1,'a',2),(1,'b',2),(2,'a',2),(2,'b',2)])

*Main> letterFSM 'b'
([0,1,2],0,[1],[(0,'a',2),(0,'b',1),(1,'a',2),(1,'b',2),(2,'a',2),(2,'b',2)])
-}

-- Machine that accepts the language {w} where w in sigma*
stringFSM :: [Char] -> FSM Int
-- (length w) + 1 should be our trap state. (length w ) should be our final state for the accepted string.
stringFSM w = ([0..(length w) + 1], 0, [(length w)], [(x, letter, final) | x <- [0..(length w) + 1], letter <- sigma, let final = if x < (length w) && letter == (w !! x) then x + 1 else (length w) + 1])

{-
*Main> stringFSM "hi"
([0,1,2,3],0,[2],[(0,'a',3),(0,'b',3),(1,'a',3),(1,'b',3),(2,'a',3),(2,'b',3),(3,'a',3),(3,'b',3)])

*Main> stringFSM "ab"
([0,1,2,3],0,[2],[(0,'a',1),(0,'b',3),(1,'a',3),(1,'b',2),(2,'a',3),(2,'b',3),(3,'a',3),(3,'b',3)])

*Main> stringFSM "ba"
([0,1,2,3],0,[2],[(0,'a',3),(0,'b',1),(1,'a',2),(1,'b',3),(2,'a',3),(2,'b',3),(3,'a',3),(3,'b',3)])

*Main> stringFSM "ababab"
([0,1,2,3,4,5,6,7],0,[6],[(0,'a',1),(0,'b',7),(1,'a',7),(1,'b',2),(2,'a',3),(2,'b',7),(3,'a',7),(3,'b',4),(4,'a',5),(4,'b',7),(5,'a',7),(5,'b',6),(6,'a',7),(6,'b',7),(7,'a',7),(7,'b',7)])
-}

-- Machine that accepts the union of the languages accepted by m1 and m2
unionFSM :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a, b)
unionFSM m1@(qs1, s1, fs1, d1) m2@(qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1, s2)
  fs = nub((fs1 >< qs2) ++ (qs1 >< fs2))
  d = nub[((q1, q2), letter, (delta (m1) (q1) (letter), delta (m2) (q2) (letter))) | (q1, q2) <- qs, letter <- sigma]

  {-
  *Main> unionFSM (letterFSM 'a')(letterFSM 'b')
([(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],(0,0),[(1,0),(1,1),(1,2),(0,1),(2,1)],[((0,0),'a',(1,2)),((0,0),'b',(2,1)),((0,1),'a',(1,2)),((0,1),'b',(2,2)),((0,2),'a',(1,2)),((0,2),'b',(2,2)),((1,0),'a',(2,2)),((1,0),'b',(2,1)),((1,1),'a',(2,2)),((1,1),'b',(2,2)),((1,2),'a',(2,2)),((1,2),'b',(2,2)),((2,0),'a',(2,2)),((2,0),'b',(2,1)),((2,1),'a',(2,2)),((2,1),'b',(2,2)),((2,2),'a',(2,2)),((2,2),'b',(2,2))])

*Main> unionFSM (emptyFSM )(letterFSM 'a')
([(0,0),(0,1),(0,2),(1,0),(1,1),(1,2)],(0,0),[(0,0),(0,1),(0,2),(1,1)],[((0,0),'a',(1,1)),((0,0),'b',(1,2)),((0,1),'a',(1,2)),((0,1),'b',(1,2)),((0,2),'a',(1,2)),((0,2),'b',(1,2)),((1,0),'a',(1,1)),((1,0),'b',(1,2)),((1,1),'a',(1,2)),((1,1),'b',(1,2)),((1,2),'a',(1,2)),((1,2),'b',(1,2))])
  -}
  
-- Machine that accepts the concatenation of the languages accepted by m1 and m2
-- helper function
powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = [x:ps | ps <- powerset xs] ++ powerset xs


catFSM :: (Eq a, Ord b) => FSM a -> FSM b -> FSM (a, [b])
catFSM m1@(qs1, s1, fs1, d1) m2@(qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = [(q, x) | q <- qs1, x <- powerset qs2, not(q `elem` fs1) || (q `elem` fs1 && s2 `elem` x)]
  s  = if s1 `elem` fs1 then (s1, [s2]) else (s1, [])
  fs = [(q, x) | (q, x ) <- qs, overlap x fs2 == True]
  d  = [(((q, x), l, (delta1, if delta1 `elem` fs1 then norm([delta (m2) (xelem) (l) | xelem <- x] ++ [s2] ) else norm[delta (m2) (xelem) (l) | xelem <- x]))) | (q, x) <- qs, l <- sigma, let delta1 = delta (m1) (q) (l)]
  
{-
*Main> catFSM (letterFSM 'a')(letterFSM 'b')
([(0,[0,1,2]),(0,[0,1]),(0,[0,2]),(0,[0]),(0,[1,2]),(0,[1]),(0,[2]),(0,[]),(1,[0,1,2]),(1,[0,1]),(1,[0,2]),(1,[0]),(2,[0,1,2]),(2,[0,1]),(2,[0,2]),(2,[0]),(2,[1,2]),(2,[1]),(2,[2]),(2,[])],(0,[]),[(0,[0,1,2]),(0,[0,1]),(0,[1,2]),(0,[1]),(1,[0,1,2]),(1,[0,1]),(2,[0,1,2]),(2,[0,1]),(2,[1,2]),(2,[1])],[((0,[0,1,2]),'a',(1,[0,2])),((0,[0,1,2]),'b',(2,[1,2])),((0,[0,1]),'a',(1,[0,2])),((0,[0,1]),'b',(2,[1,2])),((0,[0,2]),'a',(1,[0,2])),((0,[0,2]),'b',(2,[1,2])),((0,[0]),'a',(1,[0,2])),((0,[0]),'b',(2,[1])),((0,[1,2]),'a',(1,[0,2])),((0,[1,2]),'b',(2,[2])),((0,[1]),'a',(1,[0,2])),((0,[1]),'b',(2,[2])),((0,[2]),'a',(1,[0,2])),((0,[2]),'b',(2,[2])),((0,[]),'a',(1,[0])),((0,[]),'b',(2,[])),((1,[0,1,2]),'a',(2,[2])),((1,[0,1,2]),'b',(2,[1,2])),((1,[0,1]),'a',(2,[2])),((1,[0,1]),'b',(2,[1,2])),((1,[0,2]),'a',(2,[2])),((1,[0,2]),'b',(2,[1,2])),((1,[0]),'a',(2,[2])),((1,[0]),'b',(2,[1])),((2,[0,1,2]),'a',(2,[2])),((2,[0,1,2]),'b',(2,[1,2])),((2,[0,1]),'a',(2,[2])),((2,[0,1]),'b',(2,[1,2])),((2,[0,2]),'a',(2,[2])),((2,[0,2]),'b',(2,[1,2])),((2,[0]),'a',(2,[2])),((2,[0]),'b',(2,[1])),((2,[1,2]),'a',(2,[2])),((2,[1,2]),'b',(2,[2])),((2,[1]),'a',(2,[2])),((2,[1]),'b',(2,[2])),((2,[2]),'a',(2,[2])),((2,[2]),'b',(2,[2])),((2,[]),'a',(2,[])),((2,[]),'b',(2,[]))])

*Main> catFSM (emptyFSM )(letterFSM 'b')
([(0,[0,1,2]),(0,[0,1]),(0,[0,2]),(0,[0]),(1,[0,1,2]),(1,[0,1]),(1,[0,2]),(1,[0]),(1,[1,2]),(1,[1]),(1,[2]),(1,[])],(0,[0]),[(0,[0,1,2]),(0,[0,1]),(1,[0,1,2]),(1,[0,1]),(1,[1,2]),(1,[1])],[((0,[0,1,2]),'a',(1,[2])),((0,[0,1,2]),'b',(1,[1,2])),((0,[0,1]),'a',(1,[2])),((0,[0,1]),'b',(1,[1,2])),((0,[0,2]),'a',(1,[2])),((0,[0,2]),'b',(1,[1,2])),((0,[0]),'a',(1,[2])),((0,[0]),'b',(1,[1])),((1,[0,1,2]),'a',(1,[2])),((1,[0,1,2]),'b',(1,[1,2])),((1,[0,1]),'a',(1,[2])),((1,[0,1]),'b',(1,[1,2])),((1,[0,2]),'a',(1,[2])),((1,[0,2]),'b',(1,[1,2])),((1,[0]),'a',(1,[2])),((1,[0]),'b',(1,[1])),((1,[1,2]),'a',(1,[2])),((1,[1,2]),'b',(1,[2])),((1,[1]),'a',(1,[2])),((1,[1]),'b',(1,[2])),((1,[2]),'a',(1,[2])),((1,[2]),'b',(1,[2])),((1,[]),'a',(1,[])),((1,[]),'b',(1,[]))])
-}

-- Machine that accepts the Kleene star of the language accepted by m1
starFSM :: Ord a => FSM a -> FSM [a]
starFSM m1@(qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = [] ++ norm[if overlap x fs1 == True then norm(x ++ [s1]) else x | x <- powerset qs1 ]
  s  = []
  fs = [[]] ++ [x | x <- qs, overlap x fs1 == True]
  d  = [(q, l, if q == [] then if deltanew `elem` fs1 then [s1] ++ [deltanew] else [deltanew] else if finalstates `elem` nub[delta (m1) (xelem) (l) | x <- qs, xelem <- x] then norm([delta (m1) (xelem) (l) | x <- qs, xelem <- x] ++ [s1]) else norm[delta (m1) (xelem) (l) | x <- qs, xelem <- x]) | q <- qs, l <- sigma, let deltanew = delta (m1) (s1) (l), finalstates <- fs1]
  
{-
*Main> starFSM (letterFSM 'a')
([[],[0],[0,1],[0,1,2],[0,2],[2]],[],[[],[0,1],[0,1,2]],[([],'a',[0,1]),([],'b',[2]),([0],'a',[0,1,2]),([0],'b',[2]),([0,1],'a',[0,1,2]),([0,1],'b',[2]),([0,1,2],'a',[0,1,2]),([0,1,2],'b',[2]),([0,2],'a',[0,1,2]),([0,2],'b',[2]),([2],'a',[0,1,2]),([2],'b',[2])])

*Main> starFSM (stringFSM "ab")
([[],[0],[0,1],[0,1,2],[0,1,2,3],[0,1,3],[0,2],[0,2,3],[0,3],[1],[1,3],[3]],[],[[],[0,1,2],[0,1,2,3],[0,2],[0,2,3]],[([],'a',[1]),([],'b',[3]),([0],'a',[1,3]),([0],'b',[0,2,3]),([0,1],'a',[1,3]),([0,1],'b',[0,2,3]),([0,1,2],'a',[1,3]),([0,1,2],'b',[0,2,3]),([0,1,2,3],'a',[1,3]),([0,1,2,3],'b',[0,2,3]),([0,1,3],'a',[1,3]),([0,1,3],'b',[0,2,3]),([0,2],'a',[1,3]),([0,2],'b',[0,2,3]),([0,2,3],'a',[1,3]),([0,2,3],'b',[0,2,3]),([0,3],'a',[1,3]),([0,3],'b',[0,2,3]),([1],'a',[1,3]),([1],'b',[0,2,3]),([1,3],'a',[1,3]),([1,3],'b',[0,2,3]),([3],'a',[1,3]),([3],'b',[0,2,3])])
-}
  
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
