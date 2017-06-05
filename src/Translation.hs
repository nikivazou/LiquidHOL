-- Author Niki Vazou 
-- Translation of Higher Order Constructs to Refinements and back 

module Translation where

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

{-@ notRefine :: b:Bool -> ({v:Proof | b} -> False) -> {v:Proof | not b} @-}
notRefine :: Bool -> (Proof -> Proof) -> Proof
notRefine b f 
  | b         = f trivial 
  | otherwise = trivial 

notReify :: Bool -> Proof -> Proof -> Proof
{-@ notReify :: b:Bool -> {v:Proof | not b} -> ({v:Proof | b} -> False)  @-}
notReify _ notb b = trivial 



-- | Conjunction 
andRefine :: Bool -> Bool -> PAnd Proof Proof -> Proof 
{-@ 
andRefine :: b1:Bool -> b2:Bool -> PAnd {v:Proof | b1} {v:Proof | b2} 
     -> {v:Proof | b1 && b2 }
  @-}
andRefine _ _ (PAnd b1 b2) = b1 &&& b2 

andReify :: Bool -> Bool -> Proof -> PAnd Proof Proof 
{-@ 
andReify :: b1:Bool -> b2:Bool -> {v:Proof | b1 && b2 } 
     -> PAnd {v:Proof | b1} {v:Proof | b2} 
  @-}
andReify _ _ b = PAnd b b 

-- | Disjunction 

{-@ orRefine :: b1:Bool -> b2:Bool -> POr {v:Proof | b1} {v:Proof | b2}  -> {v:Proof | b1 || b2 } @-}
orRefine :: Bool -> Bool -> POr Proof Proof -> Proof
orRefine _ _ (POrLeft  p1) = p1 
orRefine _ _ (POrRight p2) = p2 

{-@ orReify :: b1:Bool -> b2:Bool -> {v:Proof | b1 || b2 } -> POr {v:Proof | b1} {v:Proof | b2}   @-}
orReify :: Bool -> Bool -> Proof -> POr Proof Proof
orReify b1 b2 p 
  | b1 = POrLeft  p 
  | b2 = POrRight p 


-- | Implication 

implRefine :: Bool -> Bool -> (Proof -> Proof) -> Proof 
{-@ implRefine :: b1:Bool -> b2:Bool -> ({v:Proof | b1} -> {v:Proof | b2}) -> {v:Proof | b1 => b2} @-}
implRefine b1 _ fb 
  | b1       = fb trivial 
  |otherwise = trivial 

implReify :: Bool -> Bool -> Proof -> (Proof -> Proof)
{-@ implReify :: b1:Bool -> b2:Bool  -> {v:Proof | b1 => b2} -> ({v:Proof | b1} -> {v:Proof | b2}) @-}
implReify _ _ b1b2 b1 = b1b2  


-- | Forall 
-- | Forall: Natural Deduction Rules 
forallElim :: (a -> Bool) -> (a -> Proof) -> a -> Proof 
{-@ forallElim :: p:(a -> Bool) -> (x:a -> {v:Proof | p x} ) -> y:a -> {v:Proof | p y} @-}
forallElim _ f y = f y 

{-@ forallIntro :: p:(a -> Bool) -> (t:a -> {v:Proof | p t}) -> (x:a -> {v:Proof | p x}) @-}
forallIntro :: (a -> Bool) -> (a -> Proof) -> (a -> Proof)
forallIntro _ f = f 

-- | Forall: Transformations cannot be made since refinements do not support forall 

-- | Exists 
-- | Exists: Natural Deduction Rules 
{-@ existsIntro :: p:(a -> Bool) -> x:a -> {v:Proof | p x} -> (y::a,{v:Proof | p y}) @-}
existsIntro :: (a -> Bool) -> a -> Proof -> (a,Proof)
existsIntro p x prop = (x, prop)

{-@ existsElim :: x:Bool -> p:(a -> Bool) -> (t::a,{v:Proof | p t}) -> (s:a -> {v:Proof | p s} -> {v:Proof | x})
           -> {v:Proof | x } @-}
existsElim :: Bool -> (a -> Bool) -> (a,Proof) -> (a -> Proof -> Proof)
           -> Proof 
existsElim x p (t, pt) f 
  = f t pt 

-- | Exists: Transformations cannot be made since refinement do not support exists 

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

