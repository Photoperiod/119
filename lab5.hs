-- CSci 119, Lab 5
-- Reference: Lecture notes, Sections 4.1, 4.2
-- Mark Philipp
-- 109941708

-- alphabet. Only inputs the machine can have. Any combination of a and b
sigma = ['a', 'b']

-- Finite State Machine M = (Q, q0, F, d)
type FSM = ([Int], Int, [Int], [(Int,Char,Int)])

-- machine that accepts at least one a
ex1 :: FSM
ex1 = ([0, 1], 0, [1], [(0, 'a', 0), (0, 'b', 1), (1, 'a', 1), (1, 'b', 1)])

-- Check whether a finite state machine (qs, q0, fs, ts) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (q0 is in qs)
-- (3) Final states are states (fs is a subset of qs; don't worry about dups)
-- (4) Transition relation is a function from qs and sigma to qs (exactly one
--     output state for each state and letter from sigma)

-- test for duplicates
noDuplicates :: [Int] -> Bool
noDuplicates [] = True           
noDuplicates (x:xs) = not (x `elem` xs) && noDuplicates xs

subset :: [Int] -> [Int] -> Bool
subset [] ys = True
subset xs [] = True
subset xs ys = and [a `elem` ys | a <- xs]

checkFSM :: FSM -> Bool
checkFSM (qs, q0, fs, ts) = noDuplicates qs && q0 `elem` qs && subset fs qs && and[or[(q, a) == (x, y) | (x, y, z) <- ts] | q <- qs, a <- sigma] && and[length [(q, a) | (x, y, z) <- ts, (q, a) == (x, y)] == 1 | q <- qs, a <- sigma]

-- Gives the transition function of the machine as a function
-- i.e., delta m q a = the state machine m goes to when reading a in state q
delta :: FSM -> Int -> Char -> Int
delta (qs, q0, fs, ts) q a = head [z | (x, y, z) <- ts, x == q, y == a]

-- Gives the delta* function
delta_star :: FSM -> Int -> [Char] -> Int
delta_star m q [] = q
delta_star m q w = delta_star m (delta (m) (q) (head w)) (tail w) 

-- Machine acceptance, Definition 1 (via delta*)
isFinalState :: FSM -> Int -> Bool
isFinalState (qs, q0, fs, ts) q = q `elem` fs

accept1 :: FSM -> [Char] -> Bool
accept1 m@(qs, q0, fs, ts) w = isFinalState m (delta_star (m) (q0) (w))

-- Machine acceptance, Definition 2 (via L_q(M))

-- accept2_aux m q w = whether m, starting in q, accepts w (recursive in w)
accept2_aux :: FSM -> Int -> [Char] -> Bool
accept2_aux m@(qs, q0, fs, ts) q [] = q `elem` fs
accept2_aux m@(qs, q0, fs, ts) q w = accept2_aux m (delta (m) (q) (head w)) (tail w)

-- Defined (non-recursively) in terms of accept2_aux
accept2 :: FSM -> [Char] -> Bool
accept2 m@(qs, q0, fs, ts) w = accept2_aux m q0 w


-- Define a machine that accepts exactly the strings with an even number of a's
-- and test it adequately
-- b*a(b*ab*)*b*
evenFSM :: FSM
evenFSM = ([0, 1, 2], 0, [2], [(0, 'a', 1), (0, 'b', 0), (1, 'a', 2), (1, 'b', 1), (2, 'a', 1), (2, 'b', 2)])
{-
*Main> checkFSM evenFSM
True
*Main> delta evenFSM 0 'a'
1
*Main> delta evenFSM 0 'b'
0
*Main> delta evenFSM 1 'a'
2
*Main> delta evenFSM 1 'b'
1
*Main> delta_star evenFSM 0 "ab"
1
*Main> delta_star evenFSM 0 "aa"
2
*Main> accept1 evenFSM "ab"
False
*Main> accept1 evenFSM "aa"
True
*Main> accept1 evenFSM "aab"
True
*Main> accept1 evenFSM "aaba"
False
*Main> accept1 evenFSM "aabaa"
True
*Main> accept1 evenFSM "aabaabbb"
True
*Main> accept2 evenFSM "ab"
False
*Main> accept2 evenFSM "aab"
True
*Main> accept2 evenFSM "aabbbb"
True
*Main> accept2 evenFSM "aabbbbaaaa"
True
*Main> accept2 evenFSM "aabbbbaaaaa"
False
-}

-- Define a machine that accepts exactly the strings that do not contain "aaa"
-- as a substring and test it adequately
tripleA :: FSM
tripleA = ([0, 1, 2, 3], 0, [0, 1, 2], [(0, 'a', 1), (0, 'b', 0), (1, 'a', 2), (1, 'b', 0), (2, 'a', 3), (2, 'b', 0), (3, 'a', 3), (3, 'b', 3)])

{-
*Main> checkFSM tripleA
True
*Main> delta tripleA 0 'a'
1
*Main> delta tripleA 1 'a'
2
*Main> delta tripleA 2 'a'
3
*Main> delta_star tripleA 0 "aab"
0
*Main> delta_star tripleA 0 "aaa"
3
*Main> delta_star tripleA 0 "aaaaaa"
3
*Main> delta_star tripleA 0 "aaaaaab"
3
*Main> delta_star tripleA 0 "bbb"
0
*Main> delta_star tripleA 0 "bba"
1
*Main> delta_star tripleA 0 "bbaa"
2
*Main> delta_star tripleA 0 "bbaaa"
3
*Main> accept1 tripleA "aab"
True
*Main> accept1 tripleA "aaba"
True
*Main> accept1 tripleA "aabaa"
True
*Main> accept1 tripleA "aaabaa"
False
*Main> accept2_aux tripleA 2 "ab"
False
*Main> accept2_aux tripleA 2 "ba"
True
*Main> accept2_aux tripleA 2 "ab"
False
*Main> accept2_aux tripleA 1 "ab"
True
*Main> accept2 tripleA "aab"
True
*Main> accept2 tripleA "aaab"
False
*Main> accept2 tripleA "aaabbbbbaaaaa"
False
-}

