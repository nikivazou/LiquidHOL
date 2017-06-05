-- Author Niki Vazou 
-- Porting Isabelle in Liquid Haskell 
-- Proofs of Isabelle tutorial 
-- https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/Isabelle2016-1/doc/prog-prove.pdf

module Chapter2 where

{-@ LIQUID "--totality" @-}
{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (length, reverse, (++))

-- | Section 2.2: Types bool, nat and list 
-- | Subsection 2.2.2: Type Nat 

{-@ data Peano [toNat] = Zero | Succ {prev :: Peano} @-} 
data Peano = Zero | Succ {prev :: Peano}

toNat :: Peano -> Int 
{-@ toNat :: Peano -> Nat @-}
{-@ measure toNat @-}
toNat Zero = 0 
toNat (Succ m) = 1 + toNat m 

{-@ reflect add @-}
add :: Peano -> Peano -> Peano 
add Zero n     = n 
add (Succ m) n = Succ (add m n)

{-@ automatic-instances add_02 @-}
add_02 :: Peano -> Proof 
{-@ add_02 :: m:Peano -> {add m Zero == m } @-}
add_02 Zero     = trivial
add_02 (Succ m) = add_02 m 


-- | Subsection 2.2.3: Type List 

data List a = N | Cons {hs :: a,  tl :: List a}
{-@ data List [length] a = N | Cons {hs :: a,  tl :: List a} @-}

length :: List a -> Int 
{-@ length :: List a -> Nat @-}
{-@ measure length @-}
length N = 0 
length (Cons _ xs) = 1 + length xs 

{-@ reflect ++ @-}
{-@ infixl ++ @-}
(++) :: List a -> List a -> List a 
N ++ ys           = ys
(Cons x xs) ++ ys = Cons x (xs ++ ys) 

reverse :: List a -> List a 
{-@ reflect reverse @-}
reverse N = N 
reverse (Cons x xs) = reverse xs ++ Cons x N

{-@ automatic-instances app_Nil2 @-}
app_Nil2 :: List a -> Proof 
{-@ app_Nil2 :: xs:List a -> {xs ++ N == xs } @-}
app_Nil2 N           = trivial
app_Nil2 (Cons _ xs) = app_Nil2 xs 

{-@ automatic-instances app_assoc @-}
{-@ app_assoc :: xs:List a -> ys:List a -> zs:List a -> {(xs ++ (ys ++ zs)) == ((xs ++ ys) ++ zs) } @-}
app_assoc :: List a -> List a -> List a -> Proof
app_assoc N _ _ = trivial
app_assoc (Cons _ xs) ys zs = app_assoc xs ys zs 

{-@ automatic-instances rev_app @-}
rev_app :: List a -> List a -> Proof
{-@ rev_app :: xs:List a -> ys:List a -> {reverse (xs ++ ys) == (reverse ys) ++ (reverse xs) } @-}
rev_app N ys = app_Nil2 (reverse ys)
rev_app (Cons x xs) ys 
  =   rev_app xs ys 
  &&& app_assoc (reverse ys) (reverse xs) (Cons x N) 

{-@ automatic-instances rev_rev @-}
{-@ rev_rev :: xs:List a -> { reverse (reverse xs) == xs } @-}
rev_rev :: List a -> Proof 
rev_rev N  = trivial
rev_rev (Cons x xs) 
  =   rev_app (reverse xs) (Cons x N) 
  &&& rev_rev xs 


-- | Section 2.3: Type and Function Definitions 

data Tree a = Tip | Node {left :: Tree a, val :: a, right :: Tree a}

{-@ data Tree [tsize] a = Tip | Node {left :: Tree a, val :: a, right :: Tree a} @-}

tsize :: Tree a -> Int 
{-@ invariant {v:Tree a | 0 <= tsize v} @-}
{-@ measure tsize @-}
tsize Tip = 0 
tsize (Node l _ r) = 1 + tsize l + tsize r  

mirror :: Tree a -> Tree a 
{-@ reflect mirror @-}
mirror Tip = Tip
mirror (Node l v r) = Node (mirror r) v (mirror l)

{-@ automatic-instances mirror_mirror @-}
mirror_mirror :: Tree a -> Proof 
{-@ mirror_mirror :: t:Tree a -> {mirror (mirror t) == t } @-}
mirror_mirror Tip = trivial 
mirror_mirror (Node l _ r) = mirror_mirror l &&& mirror_mirror r  

{-@ reflect div2 @-} 
div2 :: Peano -> Peano 
div2 Zero            = Zero
div2 (Succ Zero)     = Zero
div2 (Succ (Succ n)) = Succ (div2 n)

{-@ automatic-instances div2Eq @-}
div2Eq :: Peano -> Proof 
{-@ div2Eq :: n:Peano -> {toNat (div2 n) == (toNat n) / 2 } @-}
div2Eq Zero            = trivial 
div2Eq (Succ Zero)     = trivial 
div2Eq (Succ (Succ n)) = div2Eq n 


-- | Section 2.4: Induction Heuristics 

{-@ reflect itrev @-}
itrev :: List a -> List a -> List a 
itrev N ys           = ys 
itrev (Cons x xs) ys = itrev xs (Cons x ys)

{-@ automatic-instances lemma @-}
{-@ lemma :: xs:List a -> ys: List a -> {itrev xs ys == reverse xs ++ ys } @-}
lemma :: List a -> List a -> Proof 
lemma N _            
  = trivial 
lemma (Cons x xs) ys 
  =  lemma xs (Cons x ys)
  &&& app_assoc (reverse xs) (Cons x N) ys 

{-@ revEq :: xs:List a -> {itrev xs N == reverse xs } @-}
revEq :: List a -> Proof 
revEq xs = lemma xs N &&& app_Nil2 (reverse xs)
