{-
Mark Philipp
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
-- non-deterministic ap function from above. use norm
nap :: Ord a => [(a,Char,a)] -> a -> Char -> [a]
nap ts q a = norm [ q' | (newQ, newLetter, q') <- ts, newQ == q, newLetter == a]

-- ndelta_star m q w == normalized list of states m goes to from q on w
-- takes a whole string and determines delta of it. Recursive def. Ch. 8 page 50
ndelta_star :: Ord a => NFSM a -> a -> [Char] -> [a]
ndelta_star m q [] = [q]
ndelta_star m q (a:w) = [q'' | q' <- (nap (ndelta m) (q) (a)), q'' <- ndelta_star m q' w ]

-- naccept on page 50 too
naccept :: Ord a => NFSM a -> [Char] -> Bool
naccept m w = length [s | s <- nstarts m, overlap (ndelta_star m s w) (nfinals m)] > 0


----------------------------------------------------------------
-- Nondeterministic FSMs with epsilon moves
-- epsilon pairs (this element can transition to, this element)
-- 
data EFSM a = EFSM {
  estates :: [a],
  estarts :: [a],
  efinals :: [a],
  edelta  :: [(a,Char,a)],
  epsilon :: [(a,a)]
  }

testEFSM = EFSM { estates = [0, 1, 2, 3], estarts = [0, 3], efinals = [2], edelta = [(0, 'a', 3), (0, 'a', 0), (0, 'b', 2), (1, 'b', 1), (1, 'b', 3)], epsilon = [(0, 1), (2, 0), (3, 2)] }
-- Normalized epsilon closure of a set of states
-- (Hint: look at definition of reachable below)
-- Track all states that can be hit by epsilon
eclose :: Ord a => EFSM a -> [a] -> [a]
eclose m qs = undefined

-- edelta_star m q w == eclosed list of states m goes to from q on w
edelta_star :: Ord a => EFSM a -> a -> [Char] -> [a]
edelta_star m q w = undefined

eaccept :: Ord a => EFSM a -> [Char] -> Bool
eaccept m w = undefined


----------------------------------------------------------------
-- Machine conversions

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
nfsm_to_fsm m = undefined


-- Similar conversion from EFSM to FSM using epsilon closure
efsm_to_fsm :: Ord a => EFSM a -> FSM [a]
efsm_to_fsm m = undefined


{- Tests:

1. m and fsm_to_nfsm m accept the same strings
2. m and nfsm_to_fsm m accept the same strings
3. m and efsm_to_fsm m accept the same strings

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

