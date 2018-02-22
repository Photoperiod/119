-- Mark Philipp
-- 109941708

import Data.List (sort, subsequences)

-- Sigma = [a,b] for testing, but must work for any finite list
sigma :: [Char]
sigma = "ab"

-- Finite state machines (as records), indexed by the type of their states
-- M = FSM {states=qs, start=s, finals=fs, delta=d}, and a show instance.
data FSM a = FSM {
  states :: [a],
  start  :: a,
  finals :: [a],
  delta  :: [(a,Char,a)]
  }
instance Show a => Show (FSM a) where
  show m = "("   ++ show (states m) ++
           ", "  ++ show (start m)  ++
           ", "  ++ show (finals m) ++
           ", [" ++ steps (delta m) ++ "])" where
    steps [] = []
    steps [t] = step t
    steps (t:ts) = step t ++ "," ++ steps ts
    step (q,c,q') = show q ++ "/" ++ [c] ++ ">" ++ show q'
	
-- normalize a list, i.e., sort and remove (now adjacent) duplicates
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys
  
testFSM :: FSM [Char]
testFSM = FSM {
	states = ["empty", "a", "b", "aa", "ab", "ba", "bb"],
    start = "empty",
    finals = ["ab", "ba"],
    delta = [("empty", 'a', "a"), ("empty", 'b', "b"), ("a", 'a', "aa"), ("a", 'b', "ab"), ("b", 'a', "ba"), ("b", 'b', "bb"), ("aa", 'a', "aa"), ("aa", 'b', "aa"), ("ab", 'a', "ab"), ("ab" ,'b', "ab"), ("ba", 'a', "ba"), ("ba", 'b', "ba"), ("bb", 'a', "bb"), ("bb", 'b', "bb")]
}
  
flip :: Ord a => (a,a) -> (a,a)
flip (a,b) = if a < b then (a,b) else (b,a)

-- delta that works in reverse
deltaInv :: Ord a => FSM a -> a -> Char -> [a]
deltaInv m q a = norm [q' | (q', letter, dest) <- delta m, letter == a, dest == q]

-- I have no idea. This is basically just adding inequivalent states into a list of previously found inequivalent states until we find no more new ones
getX :: Ord a => FSM a -> [(a, a)] -> [(a, a)]
getX m [] = []
getX m qs = if length qs == length (norm [Main.flip (d1, d2) | (q1, q2) <- qs, l <- sigma, d1 <- deltaInv m q1 l, d2 <- deltaInv m q2 l]) then norm qs else norm (qs ++ (getX (m) (norm [Main.flip (d1, d2) | (q1, q2) <- qs, l <- sigma, d1 <- deltaInv m q1 l, d2 <- deltaInv m q2 l])))

-- find the final equivalent states. Any state that is in the states of m that is NOT in getX are the final equivalence states
closure :: Ord a => FSM a -> [(a, a)]
closure m = norm [Main.flip (q1, q2) | q1 <- states m, q2 <- states m, q1 /= q2, Main.flip (q1, q2) `notElem` (getX m (createInitialPairs m))]

-- get second element from equivalent pair
second :: Ord a => FSM a -> [a]
second m = norm [snd q | q <- closure m]

-- get first element from equivalent pair
first :: Ord a => FSM a -> [a]
first m = norm [fst q | q <- closure m]

-- used by start state to determine if start state is part of equivalence class
getEQState :: Ord a => FSM a -> a -> a
getEQState m q = if length ([q2 | (q1, q2) <- closure m, q == q1]) == 0 then q else head [q2 | (q1, q2) <- closure m, q == q1]

-- Find initial inequivalent states
createInitialPairs :: Ord a => FSM a -> [(a, a)]
createInitialPairs m = norm [Main.flip (q, q') | q <- states m, q' <- states m, (q' /= q) && (q' `notElem` finals m && q `elem` finals m) || (q `notElem` finals m && q' `elem` finals m)]

minimize :: Ord a => FSM a -> FSM a
minimize m = FSM {
    states = qs',
    start = s',
    finals = fs',
    delta = ds'
} where
    qs' = norm ((second m) ++ [q | q <- states m, q `notElem` first m])
    s' = getEQState m (start m)
    fs' = [q | q <- qs', q `elem` finals m]
    ds' = [(q, l, d') | (q, l, d') <- delta m, q `elem` qs', d' `elem` qs']

{-
*Main> minimize testFSM
(["a","b","ba","bb","empty"], "empty", ["ba"], ["empty"/a>"a","empty"/b>"b","b"/a>"ba","b"/b>"bb","ba"/a>"ba","ba"/b>"ba","bb"/a>"bb","bb"/b>"bb"])
-}

