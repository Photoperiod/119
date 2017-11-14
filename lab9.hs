{-
Mark Philipp
109941708
-}
-- Lab 9: Derivative-based conversion from RE' to FSM (Brzozowski Construction)

import Data.List (sort)

-- Sigma = [a,b] for testing, but must work for any finite list
sigma :: [Char]
sigma = "ab"

-- normalize a list, i.e., sort and remove (now adjacent) duplicates
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys

-- Ordinary regular expressions and a show method for them
data RE  = Empty | Letter Char | Union RE RE | Cat RE RE | Star RE

instance (Show RE) where    -- use precedence to minimize parentheses
  showsPrec d Empty         = showString "@"
  showsPrec d (Letter c)    = showString [c]
  showsPrec d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                              showsPrec 6 r1 .
                              showString "+" .
                              showsPrec 6 r2
  showsPrec d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                              showsPrec 7 r1 .
                              showsPrec 7 r2
  showsPrec d (Star Empty)  = showString "1"
  showsPrec d (Star r1)     = showsPrec 9 r1 .     -- prec(Star) = 8
                              showString "*"

-- Extended regular expressions, including a name for One = Star Empty,
-- and arbitrary numbers of arguments for (associative) Union and Cat
data RE' = Zero | One | Letter' Char | Union' [RE'] | Cat' [RE'] | Star' RE'
  deriving (Eq, Ord, Show)

-- Convert ordinary REs into extended REs
toRE' :: RE -> RE'
toRE' Empty = Zero
toRE' (Letter c) = Letter' c
toRE' (Union r1 r2) = Union' [toRE' r1, toRE' r2]
toRE' (Cat r1 r2) = Cat' [toRE' r1, toRE' r2]
toRE' (Star r1) = Star' (toRE' r1)

-- Convert extended REs into ordinary REs, eliminating Union' and Cat' on
-- lists of length < 2, and right-associating them on longer lists
toRE :: RE' -> RE
toRE Zero = Empty
toRE One = Star Empty
toRE (Letter' c) = Letter c
toRE (Union' []) = Empty
toRE (Union' [r]) = toRE r
toRE (Union' (r:rs)) = Union (toRE r) (toRE (Union' rs))
toRE (Cat' []) = Star Empty
toRE (Cat' [r]) = toRE r
toRE (Cat' (r:rs)) = Cat (toRE r) (toRE (Cat' rs))
toRE (Star' r) = Star (toRE r)

-- Basic postfix parser for RE', assuming binary + and ., including 0 and 1
re :: String -> RE'
re w = re' w [] where
  re' [] [r] = r
  re' ('0':xs) rs = re' xs (Zero:rs)
  re' ('1':xs) rs = re' xs (One:rs)
  re' ('+':xs) (r2:r1:rs) = re' xs (Union' [r1,r2]:rs)
  re' ('.':xs) (r2:r1:rs) = re' xs (Cat' [r1,r2]:rs)
  re' ('*':xs) (r:rs) = re' xs (Star' r:rs)
  re' (x:xs) rs = re' xs (Letter' x:rs)


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


-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a 
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a


-- An extended regular expression simplifier
-- give regular expression and it simplifies
simp :: RE' -> RE'
simp Zero = Zero
simp One = One
simp (Letter' c) = Letter' c
simp (Union' rs) = union' $ flat_uni $ map simp rs
simp (Cat' rs) = union' $ flat_cat $ map simp rs
simp (Star' r) = star' $ simp r

-- Smart constructor for Union' that normalizes its arguments and
-- handles the empty and singleton cases
union' :: [RE'] -> RE'
union' rs =  case norm rs of
  []  ->  Zero
  [r] -> r
  rs  -> Union' rs

-- Smart constructor for Cat' that handles the empty and singleton cases
cat' :: [RE'] -> RE'
cat' [] = One
cat' [r] = r
cat' rs = Cat' rs

-- Smart constructor for Star' that handles the constant and Star' cases
star' :: RE' -> RE'
star' Zero = One
star' One = One
star' (Star' r) = star' r
star' r = Star' r

-- Flatten a list of arguments to Union'; assumes each argument is simplified
flat_uni :: [RE'] -> [RE']
flat_uni [] = []
flat_uni (Zero:rs) = flat_uni rs
flat_uni (Union' rs':rs) = rs' ++ flat_uni rs
flat_uni (r:rs) = r : flat_uni rs

-- Flatten a list of arguments to Cat', turning them into a list of arguments
-- to Union'; assumes each argument is simplified
flat_cat :: [RE'] -> [RE']
flat_cat rs = fc [] rs where
  -- fc (args already processed, in reverse order) (args still to be processed)
  fc :: [RE'] -> [RE'] -> [RE']
  fc pr [] = [cat' $ reverse pr]
  fc pr (Zero:rs) = []
  fc pr (One:rs) = fc pr rs
  fc pr (Cat' rs':rs) = fc (reverse rs' ++ pr) rs
  fc pr (Union' rs':rs) = concat $ map (fc pr . (:rs)) rs'
  fc pr (r:rs) = fc (r:pr) rs


-- Change the states of an FSM from an equality type to Int
-- This may be useful in making converted machines easier to read
-- give FSM and it performs a renaming
intify :: Eq a => FSM a -> FSM Int
intify m = FSM {
  states = map index (states m),
  start  = index (start m),
  finals = map index (finals m),
  delta  = [(index q, a, index q') | (q,a,q') <- delta m]
  } where
    index q = lookup (states m) q
    lookup (q':qs) q = if q == q' then 0 else 1 + lookup qs q


---------------- Lab 9 begins here ----------------

-- Bypassable for extended REs, computed directly by recursion
-- byp from lab 7
byp :: RE' -> Bool
byp Zero = False
byp One = True
byp (Letter' a) = False
byp (Union' []) = undefined
byp (Union' [r]) = byp r
byp (Union' (r:rs)) = byp r || byp (Union' rs)
byp (Cat' []) = undefined
byp (Cat' [r]) = byp r
byp (Cat' (r:rs)) = byp r && byp (Cat' rs)
byp (Star' r1) = True

-- Regular-expression derivatives (aka left quotients) on extended REs,
-- computed directly.
-- left quotient from lab 7
deriv :: Char -> RE' -> RE'
deriv s Zero = Zero
deriv s One = deriv (s) (Star' Zero)
deriv s (Letter' a) = if(s == a) then Star' (Zero) else Zero
deriv s (Union' []) = undefined
deriv s (Union' [r]) = deriv (s) (r)
deriv s (Union' (r:rs)) = (Union' [(deriv s r), (deriv s (Union' rs))])
deriv s (Cat' []) = undefined
deriv s (Cat' [r]) = (deriv s r)
deriv s (Cat' (r:rs)) = if(byp r == True) then (Union' [(Cat' [(deriv s r), (Cat' rs)]), (deriv s (Cat' rs))]) else (Cat' [(deriv s r), (Cat' rs)])
deriv s (Star' r1) = (Cat' [(deriv s r1), (Star' r1)])

-- Convert an RE' to an FSM using the derivative (Brzozowski) construction.
-- States are SIMPLIFIED extended REs.  Note: to construct all the states,
-- you will have to use another closure process.
-- states = closure from lab 8. Change starting value we give it initially and our step. How we step from one state to another state
-- iterate close ([s], []). Figure out what [s] should be here.

conv :: RE' -> FSM RE'
conv r = FSM {
    states = qs',
	start = r,
	finals = fs',
	delta = d'
} where
    qs' = sort $ stable $ iterate close ([simp r], [])
    fs' = [r' | r' <- qs', byp r' == True]
    d'  = [(r', a, d) | r' <- qs', a <- sigma, let d = deriv a r']
    stable ((fr,qs):rest) = if null fr then qs else stable rest
    close (fr, xs) = (fr', xs') where  
      xs' = fr ++ xs
      fr' = norm $ filter (`notElem` xs') (concatMap step fr)
      step q = [simp (deriv a q) | a <- sigma]


-- Test, and show your tests! You may copy code from previous labs to help.

