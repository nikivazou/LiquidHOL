-- Author Niki Vazou 
-- Porting Isabelle in Liquid Haskell 
-- Proofs of Isabelle tutorial 
-- https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/Isabelle2016-1/doc/prog-prove.pdf

module Chapter3 where

{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--totality" @-}
{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
{-@ infixl ++ @-}

import Language.Haskell.Liquid.ProofCombinators
import Data.Set 

import Prelude hiding ((++), length, Either(..))
-- | Section 3.3: Proof Automation

-- forall x. exists y. x == y 
lemma_331 :: a -> (a, Proof) 
{-@ lemma_331:: x:a -> (a,Proof)<\y -> {v:Proof | x == y} > @-} 
lemma_331 x = (x,trivial)

-- A⊆B ∩C =⇒A⊆B ∪C
lemma_332 :: Set a -> Set a -> Set a -> Proof 
{-@ lemma_332 :: a:Set a -> b:Set a -> c:Set a 
              -> { (isSubsetOf a (intersection b c)) => (isSubsetOf a (union b c)) } @-} 
lemma_332 _ _ _ = trivial 

lemma_fastforce :: List a -> (List a, Proof) -> (Int, Proof)
{-@ lemma_fastforce :: xs:List a -> (ys::List a, {v:Proof | xs == ys ++ ys })
              -> (Int, Proof)<\n -> {v:Proof | length xs == n + n}> @-}
lemma_fastforce xs (ys,pf) = (length ys, lenAppend ys ys &&& pf)


{-@ 
lemma_blast :: t:(a -> a -> Bool)
            -> a:(a -> a -> Bool)
            -> (x:a -> y:a -> {t x y || t y x})
            -> (x:a -> y:a -> {a x y && a y x => x == y})
            -> (x:a -> y:a -> {t x y => a x y})
            -> x:a -> y:a -> {a x y => t x y}
            @-}
lemma_blast :: (a -> a -> Bool)
            -> (a -> a -> Bool)
            -> (a -> a -> Proof)
            -> (a -> a -> Proof)
            -> (a -> a -> Proof)
            -> a -> a -> Proof
lemma_blast t a total antis subs x y 
  =  total y x &&& antis y x &&& subs y x  

{-@ 
lemma_blast' :: t:(a -> a -> Bool)
            -> a:(a -> a -> Bool)
            -> total:(x:a -> y:a -> POr {v:Proof | t x y} {v:Proof | t y x})
            -> antis:(y:a -> x:a -> PAnd {v:Proof | a x y} {v:Proof | a y x} -> {x == y})
            -> subs:(y:a -> x:a -> {v:Proof | t y x} -> {a y x})
            -> x:a -> y:a -> {v:Proof | a x y} -> {t x y}
            @-}
lemma_blast' :: (a -> a -> Bool)
            -> (a -> a -> Bool)
            -> (a -> a -> POr Proof Proof)
            -> (a -> a -> PAnd Proof Proof -> Proof )
            -> (a -> a -> Proof -> Proof )
            -> a -> a -> Proof -> Proof 
lemma_blast' t a total antis subs x y axy 
  = case total x y of 
  	   POrLeft  txy -> txy 
  	   POrRight tyx -> antis y x (PAnd axy (subs y x tyx)) 



{-@ automatic-instances lenAppend @-}
lenAppend :: List a -> List a -> Proof 
{-@ lenAppend :: xs:List a -> ys:List a -> {length (xs ++ ys) == length xs + length ys} @-}
lenAppend N _            = trivial  
lenAppend (Cons x xs) ys = lenAppend xs ys  

-- Lists Repeat 

data List a = N | Cons {hs :: a,  tl :: List a}
{-@ data List [length] a = N | Cons {hs :: a,  tl :: List a} @-}

length :: List a -> Int 
{-@ length :: List a -> Nat @-}
{-@ measure length @-}
length N = 0 
length (Cons _ xs) = 1 + length xs 

{-@ reflect ++ @-}
(++) :: List a -> List a -> List a 
N ++ ys           = ys
(Cons x xs) ++ ys = Cons x (xs ++ ys) 





