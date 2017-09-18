{-
Mark Philipp
109941708
-}

import Data.List (nub)


---- String operations (note: String = [Char])

-- Length and concatenation (Def 2.2, reimplements len and ++)
strlen :: String -> Int
strlen [] = 0 -- |E| = 0
strlen xs = 1 + strlen (tail xs) -- |aw| = 1 + |w|

strcat :: String -> String -> String
strcat xs [] = xs -- |E * u| = u
strcat [] ys = ys
strcat xs ys = xs ++ [a | a <- ys] -- (aw) * u = a(w*u)

---- Language operations. Assume inputs contain no duplicates, and insure that
---- outputs also contain no duplicates

type Language = [String]

-- Union of languages 	Recursion probably
-- L1 ∪ L2 = {w | w ∈ L1 ∨ w ∈ L2} 
union_lang :: Language -> Language -> Language
union_lang l1 [] = l1
union_lang [] l2 = l2
union_lang l1 l2 = nub ([w | w <- l1] ++ [v | v <- l2]) 

-- Concatenation of languages (Def 2.5) 	List Comprehension
concat_lang :: Language -> Language -> Language
concat_lang l1 [] = l1
concat_lang [] l2 = l2
concat_lang l1 l2 = nub([w ++ v | w <- l1, v <- l2])

-- L^n = L * L * ... * L (n times)	recurse probably
power_lang :: Language -> Int -> Language
power_lang l 0 = []
power_lang l n = nub(concat_lang l (power_lang l (n-1)))

-- Bounded Kleene star, L* = L^0 U L^1 U L^2 U ... U L^n	Not infinite version. Use Bounded
bstar_lang :: Language -> Int -> Language
bstar_lang l 0 = []
bstar_lang l n = nub(union_lang (power_lang l n) (bstar_lang l (n-1)))

-- Reimplements elem for Languages		Dont use `elem`
element :: String -> Language -> Bool
element [] l = True -- empty string is always a member of a language
element xs l = or[ xs == w | w <- l]

-- L1 subset L2		recursion
subset :: Language -> Language -> Bool
subset [] l2 = True
subset l1 [] = True
subset l1 l2 = and [element v l2 | v <- l1] 


---- Regular expressions and the languages they denote 		Page 10 of his notes
data RegExp = Empty
             | Str String
             | Cat RegExp RegExp
             | Union RegExp RegExp
             | Star RegExp

-- [[r]], except use bound 5 for Kleene star
lang_of :: RegExp -> Language
lang_of Empty = []
lang_of (Str r) = [r]
lang_of (Union r1 r2) = union_lang (lang_of r1) (lang_of r2)
lang_of (Cat r1 r2) = concat_lang (lang_of r1) (lang_of r2)
lang_of (Star r) = bstar_lang (lang_of r) 5
              