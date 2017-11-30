-- Lab 10: REG closure under other operations
-- Mark Philipp
-- 109941708

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

-- Sigma = [a,b] for testing, but must work for any finite list
sigma :: [Char]
sigma = "ab"

-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a 
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a

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


-- Implement each of the following operations on regular expressions or FSMs

-- [[reverseRE r]] = rev([[r]]), defined by recursion on r
reverseRE :: RE -> RE
reverseRE Empty = Empty
reverseRE (Letter a) = Letter a
reverseRE (Union r1 r2) = Union (reverseRE (r1)) (reverseRE (r2))
reverseRE (Cat r1 r2) = Cat (reverseRE (r2)) (reverseRE (r1))
reverseRE (Star r1) = Star (reverseRE (r1)) 

{-
*Main> reverseRE (Letter 'a')
a
*Main> reverseRE (Cat (Letter 'a') (Letter 'b'))
ba
*Main> reverseRE (Star (Cat (Letter 'a') (Letter 'b')))
(ba)*
-}
--reverseRE = undefined

-- test FSM's
evenFSM :: FSM Int
evenFSM = FSM { states = [0, 1, 2], start = 0, finals = [2], delta = [(0, 'a', 1), (0, 'b', 0), (1, 'a', 2), (1, 'b', 1), (2, 'a', 1), (2, 'b', 2)] }

testFSM :: FSM Int
testFSM = FSM { states = [0, 1, 2], start = 0, finals = [1], delta = [(0, 'a', 1), (0, 'b', 0), (1, 'a', 2), (1, 'b', 1), (2, 'a', 0), (2, 'b', 2)]}

tripleA :: FSM Int
tripleA = FSM { states = [0, 1, 2, 3], start = 0, finals = [0, 1, 2], delta = [(0, 'a', 1), (0, 'b', 0), (1, 'a', 2), (1, 'b', 0), (2, 'a', 3), (2, 'b', 0), (3, 'a', 3), (3, 'b', 3)] }

oneA = FSM {states = [0, 1], start = 0, finals = [1], delta = [(0, 'a', 1), (0, 'b', 0), (1, 'a', 1), (1, 'b', 1)]}

oneB = FSM {states = [0, 1], start = 0, finals = [1], delta = [(0, 'a', 0), (0, 'b', 1), (1, 'a', 1), (1, 'b', 1)]}

-- L(complementFSM M) = Sigma^* - L(M)
complementFSM :: Ord a => FSM a -> FSM a
complementFSM m = FSM {
    states = (states m), 
    start = start m, 
    finals = f',
    delta = delta m
} where 
    f' = [q | q <- states m, (q `notElem` (finals m))]

{-
*Main> evenFSM
([0,1,2], 0, [2], [0/a>1,0/b>0,1/a>2,1/b>1,2/a>1,2/b>2])

*Main> complementFSM evenFSM
([0,1,2], 0, [0,1], [0/a>1,0/b>0,1/a>2,1/b>1,2/a>1,2/b>2])
-}

-- Cartesian product
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

-- L(intersectFSM m1 m2) = L(m1) intersect L(m2)
intersectFSM :: (Ord a, Ord b) => FSM a -> FSM b -> FSM (a,b)
intersectFSM m1 m2 = FSM { 
    states = (states m1) >< (states m2),
    start = ((start m1), (start m2)),
    finals = (finals m1) >< (finals m2),
    delta = d'
} where
    d' = [((q1', q2'), letter1, (d1, d2)) | (q1', letter1, d1) <- delta m1, (q2', letter2, d2) <- delta m2, letter1 == letter2]
	
{-
*Main> intersectFSM oneA oneB
([(0,0),(0,1),(1,0),(1,1)], (0,0), [(1,1)], [(0,0)/a>(1,0),(0,1)/a>(1,1),(0,0)/b>(0,1),(0,1)/b>(0,1),(1,0)/a>(1,0),(1,1)/a>(1,1),(1,0)/b>(1,1),(1,1)/b>(1,1)])

*Main> intersectFSM evenFSM tripleA
([(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)], (0,0), [(2,0),(2,1),(2,2)], [(0,0)/a>(1,1),(0,1)/a>(1,2),(0,2)/a>(1,3),(0,3)/a>(1,3),(0,0)/b>(0,0),(0,1)/b>(0,0),(0,2)/b>(0,0),(0,3)/b>(0,3),(1,0)/a>(2,1),(1,1)/a>(2,2),(1,2)/a>(2,3),(1,3)/a>(2,3),(1,0)/b>(1,0),(1,1)/b>(1,0),(1,2)/b>(1,0),(1,3)/b>(1,3),(2,0)/a>(1,1),(2,1)/a>(1,2),(2,2)/a>(1,3),(2,3)/a>(1,3),(2,0)/b>(2,0),(2,1)/b>(2,0),(2,2)/b>(2,0),(2,3)/b>(2,3)])
-}

kTest :: Char -> [Char]
kTest a | a == 'a' = "ba" 
        | a == 'b' = "bbab" 
        | otherwise = ""

barHelper :: [Char] -> RE
barHelper [] = Star (Empty)
barHelper [a] = Letter a
barHelper (a:xs) = Cat (Letter a) (barHelper xs)
 
-- [[himage r h]] = h^*([[r]]), defined by recursion on r
himage :: RE -> (Char -> [Char]) -> RE
himage Empty k = Empty
himage (Letter a) k = (barHelper (k(a)))
himage (Union r1 r2) k = Union (himage r1 k) (himage r2 k)
himage (Cat r1 r2) k = Cat (himage r1 k) (himage r2 k)
himage (Star r1) k = Star (himage r1 k)

{-
*Main> himage (Union (Cat (Letter 'a') (Letter 'b')) (Letter 'b')) kTest
babbab+bbab
-}

-- Delta star helpers
delta2 :: Eq a => FSM a -> a -> Char -> a
delta2 m = ap (delta m)

delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star = foldl . delta2

-- L(hinvimage m h) = (h^*)^{-1}(L(m))
hinvimage :: Ord a => FSM a -> (Char -> [Char]) -> FSM a
hinvimage m k = FSM{
    states = states m, 
    start = start m, 
    finals = finals m, 
    delta = d'
} where
    d' = [(q, letter, (delta_star (m) (q) (k(letter)))) | letter <- sigma, q <- states m]

{-
*Main> hinvimage oneA kTest
([0,1], 0, [1], [0/a>1,1/a>1,0/b>1,1/b>1])

*Main> hinvimage testFSM kTest
([0,1,2], 0, [1], [0/a>1,1/a>2,2/a>0,0/b>1,1/b>2,2/b>0])

*Main> hinvimage evenFSM kTest
([0,1,2], 0, [2], [0/a>1,1/a>2,2/a>1,0/b>1,1/b>2,2/b>1])
-}
	
	
-- L(rightq m a) = { w | wa in L(m) }
rightq :: Ord a => FSM a -> Char -> FSM a
rightq m a = FSM {
    states = states m,
    start = start m,
    finals = f',
	delta = delta m
} where
    f' =  [q | q <- states m, (delta_star m q [a]) `elem` (finals m)]

{-
*Main> rightq oneA 'a'
([0,1], 0, [0,1], [0/a>1,0/b>0,1/a>1,1/b>1])

*Main> rightq oneB 'a'
([0,1], 0, [1], [0/a>0,0/b>1,1/a>1,1/b>1])

*Main> rightq oneB 'b'
([0,1], 0, [0,1], [0/a>0,0/b>1,1/a>1,1/b>1])

*Main> rightq oneA 'b'
([0,1], 0, [1], [0/a>1,0/b>0,1/a>1,1/b>1])
-}

-- Note: left quotient was already implemented in a previous lab
