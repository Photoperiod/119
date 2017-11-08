{-
Mark Philipp
109941708
-}

-- Lab 8: Non-deterministic finite state machines
-- Feel free to use any additional functions from previous labs

import Data.List (sort, subsequences)

-- normalize a list, i.e., sort and remove (now adjacent) duplicates
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys

-- Sigma = [a,b] for testing, but must work for any finite list
sigma :: [Char]
sigma = "ab"

-- Finite state machines (as records), indexed by the type of their states
-- M = FSM {states=qs, start=s, finals=fs, delta=d}
data FSM a = FSM {
  states :: [a],
  start  :: a,
  finals :: [a],
  delta  :: [(a,Char,a)]
  }

-- Output format for FSMs
instance Show a => Show (FSM a) where
  show m = "("   ++ show (states m) ++
           ", "  ++ show (start m)  ++
           ", "  ++ show (finals m) ++
           ", [" ++ steps (delta m) ++ "])" where
    steps [] = []
    steps [t] = step t
    steps (t:ts) = step t ++ "," ++ steps ts
    step (q,c,q') = show q ++ "/" ++ [c] ++ ">" ++ show q'
	
instance Show a => Show (NFSM a) where
  show m = "("   ++ show (nstates m) ++
           ", "  ++ show (nstarts m)  ++
           ", "  ++ show (nfinals m) ++
           ", [" ++ steps (ndelta m) ++ "])" where
    steps [] = []
    steps [t] = step t
    steps (t:ts) = step t ++ "," ++ steps ts
    step (q,c,q') = show q ++ "/" ++ [c] ++ ">" ++ show q'

instance Show a => Show (EFSM a) where
  show m = "("   ++ show (estates m) ++
           ", "  ++ show (estarts m)  ++
           ", "  ++ show (efinals m) ++
           ", [" ++ steps (edelta m) ++ "]" where
    steps [] = []
    steps [t] = step t
    steps (t:ts) = step t ++ "," ++ steps ts
    step (q,c,q') = show q ++ "/" ++ [c] ++ ">" ++ show q'

-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a 
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a


---- Lab 8 begins here -----------------------------------------------------

-- Nondeterministic FSMs
data NFSM a = NFSM {
  nstates :: [a],  
  nstarts :: [a],
  nfinals :: [a],
  ndelta  :: [(a,Char,a)]
  }

testNFSM = NFSM { nstates = [0, 1, 2], nstarts = [0, 1], nfinals = [2], ndelta = [(0, 'b', 1), (1, 'a', 0),(1, 'a', 2), (2, 'b', 2)]}
 
-- nap ts q a == the normalized list of q' such that (q, a, q') is in ts
nap :: Ord a => [(a,Char,a)] -> a -> Char -> [a]
nap ts q a = norm [ q' | (newQ, newLetter, q') <- ts, newQ == q, newLetter == a]

-- ndelta_star m q w == normalized list of states m goes to from q on w
ndelta_star :: Ord a => NFSM a -> a -> [Char] -> [a]
ndelta_star m q [] = [q]
ndelta_star m q (a:w) = [q'' | q' <- (nap (ndelta m) (q) (a)), q'' <- ndelta_star m q' w ]

naccept :: Ord a => NFSM a -> [Char] -> Bool
naccept m w = length [s | s <- nstarts m, overlap (ndelta_star m s w) (nfinals m)] > 0


----------------------------------------------------------------
-- Nondeterministic FSMs with epsilon moves

data EFSM a = EFSM {
  estates :: [a],
  estarts :: [a],
  efinals :: [a],
  edelta  :: [(a,Char,a)],
  epsilon :: [(a,a)]
  }

testEFSM = EFSM { estates = [0, 1, 2, 3], estarts = [0, 3], efinals = [1, 2], edelta = [(0, 'a', 3), (0, 'a', 0), (0, 'b', 2), (1, 'b', 1), (1, 'b', 3)], epsilon = [(0, 1), (2, 0), (3, 2)] }
-- Normalized epsilon closure of a set of states
-- (Hint: look at definition of reachable below)
-- Track all states that can be hit by epsilon
eclose :: Ord a => EFSM a -> [a] -> [a]
eclose m qs = sort $ stable $ iterate close (qs, []) where
              stable ((fr,qs):rest) = if null fr then qs else stable rest
              -- in close (fr, xs), fr (frontier) and xs (current closure) are disjoint
              close (fr, xs) = (fr', xs') where
                xs' = fr ++ xs
                fr' = norm $ filter (`notElem` xs') (concatMap step fr)
                step q = norm [q' | (qfr, q')<-epsilon m, qfr == q]				

-- edelta_star m q w == eclosed list of states m goes to from q on w
edelta_hat :: Ord a => EFSM a -> a -> Char -> [a]
edelta_hat m q a = norm [d | (q', letter, d) <- edelta m, x <- (powerset (estates m)), q' == q, letter == a]

edelta_star :: Ord a => EFSM a -> a -> [Char] -> [a]
edelta_star m q [] = eclose m [q]
edelta_star m q (a:w) = norm [finalD | hat <- (eclose m (edelta_hat m q a)), finalD <- (edelta_star m hat w)]

eaccept :: Ord a => EFSM a -> [Char] -> Bool
eaccept m w = length [w | s <- eclose m (estarts m), overlap (edelta_star m s w) (efinals m)] > 0


----------------------------------------------------------------
-- Machine conversions

-- helper functions
powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = [x:ps | ps <- powerset xs] ++ powerset xs

subset :: Eq a => [a] -> [a] -> Bool
subset [] ys = True
subset (x:xs) ys = elem x ys && subset xs ys

testFSM = FSM {states = [1, 2], start = 1, finals = [2], delta = [(1, 'a', 2), (1, 'b', 1), (2, 'a', 2), (2, 'b', 2)]}
testNFSM2 = NFSM {nstates = [1, 2, 3], nstarts = [1, 2], nfinals = [3], ndelta = [(1, 'a', 1), (1, 'a', 3), (1, 'b', 2), (2, 'b', 2), (2, 'b', 3), (3, 'a', 3)]}
testEFSM2 = EFSM {estates = [1, 2, 3], estarts = [1], efinals = [3], edelta = [(1, 'a', 1), (2, 'b', 2), (3, 'a', 3)], epsilon = [(1, 2), (2, 3)]}
testEFSM3 = EFSM {estates = [1, 2, 3], estarts = [1], efinals = [2], edelta = [(1, 'a', 1), (1, 'a', 2), (2, 'b', 2)], epsilon = [(2, 3)]}
testEFSM4 = EFSM {estates = [1, 2, 3], estarts = [1], efinals = [2], edelta = [(2, 'a', 2), (2, 'b', 3), (3, 'a', 3), (3, 'b', 3)], epsilon = [(1, 2)]}

-- Easy conversion from FSM to NFSM (given)
fsm_to_nfsm :: Eq a => FSM a -> NFSM a
fsm_to_nfsm m = NFSM {
  nstates = states m,
  nstarts = [start m],
  nfinals = finals m,
  ndelta  = delta m
  }


-- Conversion from NFSM to FSM by the "subset construction"
nfsm_to_fsm :: Ord a => NFSM a -> FSM [a]
nfsm_to_fsm m = FSM { states = qs, start = s, finals = fs, delta = ds } where
              qs = norm (powerset (nstates m))
              s = nstarts m
              fs = norm [q | q <- qs, overlap (q) (nfinals m)]
              ds = norm [(qElement, letter, norm [q'' | (qIter, letter2, q'') <- (ndelta m), qIter `elem` qElement, letter2 == letter]) | (q, letter, q') <- (ndelta m), qElement <- qs]


-- Similar conversion from EFSM to FSM using epsilon closure
efsm_to_fsm :: Ord a => EFSM a -> FSM [a]
efsm_to_fsm m = FSM {states = qs, start = s, finals = fs, delta = ds} where
              qs = norm (powerset (estates m))
              s = eclose m (estarts m)
              fs = norm [q | q <- qs, overlap (q) (efinals m)]
              ds = norm [(qElement, letter, (eclose (m) (norm [q'' | (qIter, letter2, q'') <- (edelta m), qIter `elem` qElement, letter2 == letter]))) | (q, letter, q') <- (edelta m), qElement <- qs]

			  
-- FSM Accept functions
delta2 :: Eq a => FSM a -> a -> Char -> a
delta2 m = ap (delta m)

delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star = foldl . delta2

accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m w = elem (delta_star (m) (start m) (w)) (finals m)

accept2_aux :: Eq a => FSM a -> a -> [Char] -> Bool
accept2_aux m q [] = elem (q) (finals m)
accept2_aux m q (a:w) = accept2_aux (m) (delta2 m q a) (w)

accept2 :: Eq a => FSM a -> [Char] -> Bool
accept2 m w = accept2_aux (m) (start m) (w)

{- Tests:

1. m and fsm_to_nfsm m accept the same strings
*Main> accept1 testFSM "ab"
True
*Main> accept1 testFSM "b"
False
*Main> accept1 testFSM "bbbb"
False
*Main> accept1 testFSM "bbbba"
True

*Main> naccept (fsm_to_nfsm (testFSM)) "ab"
True
*Main> naccept (fsm_to_nfsm (testFSM)) "b"
False
*Main> naccept (fsm_to_nfsm (testFSM)) "bbbb"
False
*Main> naccept (fsm_to_nfsm (testFSM)) "bbbba"
True

2. m and nfsm_to_fsm m accept the same strings
*Main> naccept testNFSM2 "ba"
True
*Main> naccept testNFSM2 "bab"
False
*Main> naccept testNFSM2 "aba"
False
*Main> naccept testNFSM2 "ab"
False
*Main> naccept testNFSM2 "abb"
True

*Main> accept1 (nfsm_to_fsm testNFSM2) "ba"
True
*Main> accept1 (nfsm_to_fsm testNFSM2) "bab"
False
*Main> accept1 (nfsm_to_fsm testNFSM2) "aba"
False
*Main> accept1 (nfsm_to_fsm testNFSM2) "ab"
False
*Main> accept1 (nfsm_to_fsm testNFSM2) "abb"
True

3. m and efsm_to_fsm m accept the same strings
*Main> eaccept testEFSM4 ""
True
*Main> eaccept testEFSM4 "a"
True
*Main> eaccept testEFSM4 "ab"
False
*Main> eaccept testEFSM4 "abbb"
False
*Main> eaccept testEFSM4 "abbba"
False
*Main> eaccept testEFSM4 "aa"
True
*Main> eaccept testEFSM4 "aaaaaaa"
True

*Main> accept1 (efsm_to_fsm testEFSM4) ""
True
*Main> accept1 (efsm_to_fsm testEFSM4) "a"
True
*Main> accept1 (efsm_to_fsm testEFSM4) "ab"
False
*Main> accept1 (efsm_to_fsm testEFSM4) "abbb"
False
*Main> accept1 (efsm_to_fsm testEFSM4) "abbba"
False
*Main> accept1 (efsm_to_fsm testEFSM4) "aa"
True
*Main> accept1 (efsm_to_fsm testEFSM4) "aaaaaaa"
True
-}


---- Lab 8 ends here ----------------------------------------------------

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable (FSM {states=qs, start=s, finals=fs, delta=d}) =
  FSM {states=qs', start=s, finals=fs', delta=d'} where
    qs' = sort $ stable $ iterate close ([s], []) -- use this for closure
    fs' = filter (`elem` qs') fs
    d'  = filter (\(q,_,_) -> q `elem` qs') d
    stable ((fr,qs):rest) = if null fr then qs else stable rest
    -- in close (fr, xs), fr (frontier) and xs (current closure) are disjoint
    close (fr, xs) = (fr', xs') where  
      xs' = fr ++ xs
      fr' = norm $ filter (`notElem` xs') (concatMap step fr) -- for every state in frontier, transition and keep track of where you went
      step q = map (ap d q) sigma


-- Change the states of an FSM from an equality type to Int
intify :: Eq a => FSM a -> FSM Int
intify m = FSM {
  states = map index (states m),
  start  = index (start m),
  finals = map index (finals m),
  delta  = [(index q, a, index q') | (q,a,q') <- delta m]
  } where
    index q = lookup (states m) q
    lookup (q':qs) q = if q == q' then 0 else 1 + lookup qs q

