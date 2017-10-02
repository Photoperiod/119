-- CSci 119, Lab 5
-- Reference: Lecture notes, Sections 4.1, 4.2
-- Mark Philipp
-- 109941708

sigma = ['a', 'b']

-- Finite State Machine M = (Q, q0, F, d)
type FSM = ([Int], Int, [Int], [(Int,Char,Int)])

-- Check whether a finite state machine (qs, q0, fs, ts) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (q0 is in qs)
-- (3) Final states are states (fs is a subset of qs; don't worry about dups)
-- (4) Transition relation is a function from qs and sigma to qs (exactly one
--     output state for each state and letter from sigma)
checkFSM :: FSM -> Bool
checkFSM (qs, q0, fs, ts) = undefined

-- Gives the transition function of the machine as a function
-- i.e., delta m q a = the state machine m goes to when reading a in state q
delta :: FSM -> Int -> Char -> Int
delta (qs, q0, fs, ts) q a = undefined

-- Gives the delta* function
delta_star :: FSM -> Int -> [Char] -> Int
delta_star m q w = undefined

-- Machine acceptance, Definition 1 (via delta*)
accept1 :: FSM -> [Char] -> Bool
accept1 m w = undefined


-- Machine acceptance, Definition 2 (via L_q(M))

-- accept2_aux m q w = whether m, starting in q, accepts w (recursive in w)
accept2_aux :: FSM -> Int -> [Char] -> Bool
accept2_aux m q w = undefined

-- Defined (non-recursively) in terms of accept2_aux
accept2 :: FSM -> [Char] -> Bool
accept2 m w = undefined


-- Define a machine that accepts exactly the strings with an even number of a's
-- and test it adequately


-- Define a machine that accepts exactly the strings that do not contain "aaa"
-- as a substring and test it adequately





