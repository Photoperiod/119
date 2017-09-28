-- CSci 119, Lab 4
import Data.List
---- Regular expressions, along with input and output
data RegExp = Empty
             | Letter Char
             | Union RegExp RegExp
             | Cat RegExp RegExp
             | Star RegExp

instance (Show RegExp) where    -- use precedence to minimize parentheses
  showsPrec d Empty         = showString "@"
  showsPrec d (Letter c)    = showString [c]
  showsPrec d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                              showsPrec 6 r1 .
                              showString "+" .
                              showsPrec 6 r2
  showsPrec d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                              showsPrec 7 r1 .
                              showsPrec 7 r2
  showsPrec d (Star r1)     = showsPrec 9 r1 .     -- prec(Star) = 8
                              showString "*"

-- Quick and dirty postfix regex parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Union r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Letter x:rs)


---------------- Part 1 ----------------

-- Implement the six recursive predications/operations on RegExp given in
-- Section 3.3 of the notes. Each should begin with a type declaration.
-- Include several tests for each function.

-- emptiness (Empty) returns true
-- emptiness (Letter 'a') returns false
-- emptiness (Union (Empty) (Letter 'a')) false
-- emptiness (Cat (Empty) (Letter 'a')) returns true
-- emptiness (Star (Letter 'h')) returns false
emptiness :: RegExp -> Bool
emptiness Empty = True
emptiness (Letter a) = False
emptiness (Union r1 r2) = emptiness r1 && emptiness r2
emptiness (Cat r1 r2) = emptiness r1 || emptiness r2
emptiness (Star r1) = False

-- unitarity (Empty) returns false
-- unitarity (Letter 'a') returns false
-- unitarity  (Union (Star (Empty)) (Empty)) returns true
-- unitarity (Cat (Empty) (Letter 'a')) returns false
-- unitarity (Star (Empty)) returns true
unitarity :: RegExp -> Bool
unitarity Empty = False
unitarity (Letter a) = False
unitarity (Union r1 r2) = (unitarity r1 && emptiness r2) || (emptiness r1 && unitarity r2) || (unitarity r1 && unitarity r2)
unitarity (Cat r1 r2) = (unitarity r1) && (unitarity r2)
unitarity (Star r1) = emptiness r1 || unitarity r1

-- bypassability (Empty) returns false
-- bypassability (Letter 'a') returns false
-- bypassability (Union (Star (Empty)) (Letter 'a')) returns true
-- bypassability (Cat (Empty) (Letter 'a')) returns false
-- bypassability (Star (Empty)) returns true
bypassability :: RegExp -> Bool
bypassability Empty = False
bypassability (Letter a) = False
bypassability (Union r1 r2) = bypassability r1 || bypassability r2
bypassability (Cat r1 r2) = bypassability r1 && bypassability r2
bypassability (Star r1) = True

-- infiniteness Empty returns false
-- infiniteness (Letter 'b') returns false
-- infiniteness (Union (Star (Letter 'a')) (Empty)) returns true
-- infiniteness infiniteness (Cat (Union (Star (Letter 'a')) (Empty)) (Letter 'a')) returns true
-- infiniteness (Star (Letter 'a')) returns true
-- infiniteness (Star (Empty)) returns false
infiniteness :: RegExp -> Bool
infiniteness Empty = False
infiniteness (Letter a) = False
infiniteness (Union r1 r2) = infiniteness r1 || infiniteness r2
infiniteness (Cat r1 r2) = (infiniteness r1 && not(emptiness r2)) || (infiniteness r2 && not(emptiness r1))
infiniteness (Star r1) = not(emptiness r1) && not(unitarity r1)

-- reversal Empty returns @
-- reversal (Letter 'B') returns B
-- reversal (Union (Union (Letter 'H') (Letter 'i')) (Union (Union (Letter 'B') (Letter 'y')) (Letter 'e'))) returns H+i+B+y+e
-- reversal (Cat (Letter 'H') (Letter 'i')) returns iH
-- reversal (Cat (Union (Letter 'H' ) (Letter 'i')) (Union (Letter 'B') (Letter 'i'))) returns (B+i)(H+i)
-- (Star (Cat (Letter 'H') (Letter 'i'))) returns (iH)*
reversal :: RegExp -> RegExp
reversal Empty = Empty
reversal (Letter a) = (Letter a)
reversal (Union r1 r2) = (Union (reversal r1) ( reversal r2))
reversal (Cat r1 r2) = (Cat (reversal r2) ( reversal r1))
reversal (Star r1) = (Star (reversal r1))

--leftquotient 'a' Empty returns @
-- leftquotient 'h' (Letter 'h') returns @*
-- leftquotient 'h' (Union (Cat (Letter 'h') (Letter 'i')) (Cat (Letter 'b') (Letter 'i'))) returns @*i+@i
-- leftquotient 'h' (Cat (Cat (Letter 'h') (Letter 'i')) (Cat (Cat (Letter 'b' ) (Letter 'y')) (Letter 'e'))) returns @*ibye
-- leftquotient 'a' (Star (Letter 'b')) returns @b*
leftquotient :: Char -> RegExp -> RegExp
leftquotient s Empty = Empty
leftquotient s (Letter a) = if (s == a) then Star(Empty) else Empty
leftquotient s (Union r1 r2) = (Union (leftquotient s r1) ( leftquotient s r2))
leftquotient s (Cat r1 r2) = if (bypassability r1 == True) then (Cat(Cat (leftquotient s r1) r2) (leftquotient s r2)) else (Cat (leftquotient s r1) (r2))
leftquotient s (Star r1) = (Cat (leftquotient s r1) (Star r1))

---------------- Part 2 ----------------

-- Implement the two matching algorithms given in Section 3.4 of the notes.
-- Call them match1 and match2. Start by implementing splits:

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]
-- [splitAt 3 xs]
-- [([head w2], w2) | w2 <- droplist xs]
droplist :: [a] -> [a]-> [([a], [a])]
droplist [] [] = []
droplist xs [] = [(xs, [])]
droplist [] (y:ys) = [([], y:ys)] ++ droplist ([y]) (ys)
droplist (xs) (y:ys) = [(xs, y:ys)] ++ droplist (xs ++ [y]) (ys)

splits :: [a] -> [([a], [a])]
splits [] = []
splits xs = droplist [] xs

match1 :: RegExp -> String -> Bool
match1 r w = undefined


match2 :: RegExp -> String -> Bool
match2 r w = undefined



-- Some regular expressions for testing. Also, test them on other solutions
-- to the exercises of Section 3.2 (as many as you can get).

ab   = toRE "aa.bb.+*"            -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE "b*a.b*.a.*b*."       -- even number of a's
bb1  = toRE "aba.+*b.b.aab.+*."   -- contains bb exactly once