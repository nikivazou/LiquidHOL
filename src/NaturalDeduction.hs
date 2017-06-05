-- Author Niki Vazou 
-- Encoding of Natural Deduction Rules in Liquid Haskell 
-- First  order rules: http://www.cs.cornell.edu/courses/cs3110/2013sp/lectures/lec15-logic-contd/lec15.html
-- Higher order rules: http://hume.ucdavis.edu/mattey/phi112/112dedurles_ho.pdf

module NaturalDeduction where

{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--totality" @-}

import Language.Haskell.Liquid.ProofCombinators


{-
-- Expressive Power is HOL: 
-- Translation from HOL -> Liquid Types: 

True       |-> {v:Proof | true }
False      |-> {v:Proof | false }
not form   |-> F -> {v:Proof | false }
f1 && f2   |-> PAnd F1 F2 
f1 || f2   |-> POr F1 F2 
f1 => f2   |-> (F1 -> F2)
forall x.f |-> x:a -> F 
exists x.f |-> (a,Proof)<\x -> F> 
-}

{-@ type False = {v:Proof | false} @-}
{-@ type True  = {v:Proof | true } @-}

-- | Negation 
{-@ notIntro :: b:Bool -> ({v:Proof | b} -> False) -> {v:Proof | not b} @-}
notIntro :: Bool -> (Proof -> Proof) -> Proof
notIntro b f 
  | b         = f trivial 
  | otherwise = trivial 

notElim :: Bool -> Proof -> Proof -> Proof
{-@ notElim :: b:Bool -> {v:Proof | not b} -> ({v:Proof | b} -> False)  @-}
notElim _ notb b = trivial 

-- | Conjunction 
andIntro :: Bool -> Bool -> PAnd Proof Proof 
{-@ 
andIntro :: b1:{Bool | b1} -> b2:{Bool | b2} -> PAnd {v:Proof | b1} {v:Proof | b2} 
  @-}
andIntro b1 b2 = PAnd trivial trivial 

andElimLeft :: Bool -> Bool -> PAnd Proof Proof -> Proof 
{-@ 
andElimLeft :: b1:Bool -> b2:Bool -> PAnd {v:Proof | b1} {v:Proof | b2} 
     -> {v:Proof | b1 }
  @-}
andElimLeft _ _ (PAnd b1 b2) = b1  

andElimRight :: Bool -> Bool -> PAnd Proof Proof -> Proof 
{-@ 
andElimRight :: b1:Bool -> b2:Bool -> PAnd {v:Proof | b1} {v:Proof | b2} 
     -> {v:Proof | b2 }
  @-}
andElimRight _ _ (PAnd b1 b2) = b2  


-- | Disjunction 

orIntroLeft :: Bool -> Bool -> Proof -> POr Proof Proof 
{-@ 
orIntroLeft :: b1:Bool -> b2:Bool -> {v:Proof | b1}  -> POr {v:Proof | b1} {v:Proof | b2} 
  @-}
orIntroLeft _ _ p = POrLeft p


orIntroRight :: Bool -> Bool -> Proof -> POr Proof Proof 
{-@ 
orIntroRight :: b1:Bool -> b2:Bool -> {v:Proof | b2}  -> POr {v:Proof | b1} {v:Proof | b2} 
  @-}
orIntroRight _ _ p = POrRight p


orElim :: Bool -> Bool -> Bool -> POr Proof Proof -> (Proof -> Proof) -> (Proof -> Proof) -> Proof 
{-@ orElim :: p:Bool -> q:Bool -> r:Bool 
           -> POr {v:Proof | p} {v:Proof | q} 
           -> ({v:Proof | p} -> {v:Proof | r}) 
           -> ({v:Proof | q} -> {v:Proof | r}) 
           -> {v:Proof | r} @-}
orElim _ _ _ (POrLeft  p) fp _ = fp p 
orElim _ _ _ (POrRight q) _ fq = fq q 


-- | Implication 
implElim :: Bool -> Bool -> Proof -> (Proof -> Proof) -> Proof 
{-@ implElim :: p:Bool -> q:Bool -> {v:Proof | p} -> ({v:Proof | p} -> {v:Proof | q}) 
                -> {v:Proof | q} @-}
implElim _ _ p f = f p


-- | Forall 
forallElim :: (a -> Bool) -> (a -> Proof) -> a -> Proof 
{-@ forallElim :: p:(a -> Bool) -> (x:a -> {v:Proof | p x} ) -> y:a -> {v:Proof | p y} @-}
forallElim _ f y = f y 

{-@ forallIntro :: p:(a -> Bool) -> (t:a -> {v:Proof | p t}) -> (x:a -> {v:Proof | p x}) @-}
forallIntro :: (a -> Bool) -> (a -> Proof) -> (a -> Proof)
forallIntro _ f = f 

-- | Exists 
{-@ existsIntro :: p:(a -> Bool) -> x:a -> {v:Proof | p x} -> (y::a,{v:Proof | p y}) @-}
existsIntro :: (a -> Bool) -> a -> Proof -> (a,Proof)
existsIntro p x prop = (x, prop)

{-@ existsElim :: x:Bool -> p:(a -> Bool) -> (t::a,{v:Proof | p t}) -> (s:a -> {v:Proof | p s} -> {v:Proof | x})
           -> {v:Proof | x } @-}
existsElim :: Bool -> (a -> Bool) -> (a,Proof) -> (a -> Proof -> Proof)
           -> Proof 
existsElim x p (t, pt) f 
  = f t pt 


-- Extra Natural Deduction Rules 
modusPonens :: Bool -> Bool -> Proof -> (Proof -> Proof) -> Proof 
{-@ modusPonens :: p:Bool -> q:Bool -> {v:Proof | p} -> ({v:Proof | p} -> {v:Proof | q}) 
                -> {v:Proof | q} @-}
modusPonens _ _ p f = f p


reductioAdAbsurdum :: Bool -> (Proof -> Proof) -> Proof
{-@ reductioAdAbsurdum :: b:Bool -> ({v:Proof | not b} -> False) -> {v:Proof | b} @-}
reductioAdAbsurdum b f
  | b         = trivial
  | otherwise = f trivial

exFalsoQuodlibe :: Bool -> Proof -> Proof
{-@ exFalsoQuodlibe :: b:Bool -> False -> Proof @-}
exFalsoQuodlibe _ _ = trivial

{-@ excludedMiddle :: b:Bool -> {v:Proof | b || (not b)} @-}
excludedMiddle :: Bool -> Proof 
excludedMiddle _ = trivial 

