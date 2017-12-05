-- Mark Philipp
-- 109941708

import Data.List (sort, subsequences)

-- Sigma = [a,b] for testing, but must work for any finite list
sigma :: [Char]
sigma = "ab"
-- Cartesian product
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

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

closure :: Ord a => FSM a -> [a] -> [a]
closure m qs = sort $ stable $ iterate close (qs, []) where
              stable ((fr,qs):rest) = if null fr then qs else stable rest
              -- in close (fr, xs), fr (frontier) and xs (current closure) are disjoint
              close (fr, xs) = (fr', xs') where
                xs' = fr ++ xs
                fr' = norm $ filter (`notElem` xs') (concatMap step fr)
                step q = norm [q' | (qfr, q')<-(createPairs (states m)), qfr == q]	

--createPairs :: Ord a => [a] -> [(a, a)]
--createPairs qs = norm [Main.flip (q, q') | q <- qs, q' <- qs, q' /= q]

createInitialPairs :: Ord a => FSM a -> [(a, a)]
createInitialPairs m = norm [Main.flip (q, q') | q <- states m, q' <- states m, (q' /= q) && (q' `notElem` finals m && q `elem` finals m) || (q `notElem` finals m && q' `elem` finals m)]

minimize :: Ord a => FSM a -> FSM a
minimize m = FSM {
    states = undefined, --[(q', [q'' | q'' <- states m, (q' `elem` finals m && q'' `notElem` finals m) || (q'' `elem` finals m && q' `notElem` finals m)]) | q' <- states m],
    start = start m,
    finals = undefined,
    delta = undefined
}

--deltainv :: Ord a => a -> Char -> [a]
--deltainv q a = [q' | delta q' a = q]

