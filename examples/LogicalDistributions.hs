-- Author Niki Vazou 
-- Natural Deduction Rules for Quantifiers
-- Proofs from http://hume.ucdavis.edu/mattey/phi112/112dedurles_ho.pdf

module Examples where

{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--totality" @-}

import Language.Haskell.Liquid.ProofCombinators

-- Universal Introduction
{-@ 
ex1 :: f:(a -> Bool) -> g:(a -> Bool)
    -> (x:a -> PAnd {v:Proof | f x} {v:Proof | g x})
    -> (y:a -> {v:Proof | f y})
  @-}
ex1 :: (a -> Bool) -> (a -> Bool)
    -> (a -> PAnd Proof Proof)
    -> (a -> Proof)
ex1 f g assumption y = 
  case assumption y of 
    PAnd fy _ -> fy  


class NonEmpty a where
  pick :: a 

-- Existential Introduction

{-@ ex2 :: f:(a -> Bool) -> (x:a -> {v:Proof | f x})
    -> (y::a,{v:Proof | f y}) @-}
ex2 :: NonEmpty a => (a -> Bool) -> (a -> Proof) -> (a,Proof)
ex2 f fx = (y, fx y)
  where
    y = pick


-- Existential Elimination 
{-@ existsAllDistr :: f:(a -> Bool) -> g:(a -> Bool) -> (x::a, PAnd {v:Proof | f x} {v:Proof | g x})
    -> PAnd (x::a, {v:Proof | f x}) (x::a, {v:Proof | g x}) @-}
existsAllDistr :: (a -> Bool) -> (a -> Bool) -> (a,PAnd Proof Proof) -> PAnd (a,Proof) (a,Proof)
existsAllDistr f g (x,PAnd fx gx) = PAnd (x,fx) (x,gx)


{-@ existsOrDistr :: f:(a -> Bool) -> g:(a -> Bool) -> (x::a, POr {v:Proof | f x} {v:Proof | g x})
    -> POr (x::a, {v:Proof | f x}) (x::a, {v:Proof | g x}) @-}
existsOrDistr :: (a -> Bool) -> (a -> Bool) -> (a,POr Proof Proof) -> POr (a,Proof) (a,Proof)
existsOrDistr f g (x,POrLeft fx)  = POrLeft  (x,fx) 
existsOrDistr f g (x,POrRight fx) = POrRight (x,fx) 


{-@ forallAndDistr :: f:(a -> Bool) -> g:(a -> Bool) -> (x:a -> PAnd {v:Proof | f x} {v:Proof | g x})
    -> PAnd (x:a -> {v:Proof | f x}) (x:a -> {v:Proof | g x}) @-}
forallAndDistr :: (a -> Bool) -> (a -> Bool) -> (a -> PAnd Proof Proof) -> PAnd (a -> Proof) (a -> Proof)
forallAndDistr f g andx 
  = PAnd (\x -> case andx x of PAnd fx _ -> fx)
         (\x -> case andx x of PAnd _ gx -> gx)


{-@ forallExistsImpl :: p:(a -> Bool) -> q:(a -> a -> Bool)
  -> (x:a -> (y::a, {v:Proof | p x} -> {v:Proof | q x y} ))
  -> (x:a -> ({v:Proof | p x} -> (y::a, {v:Proof | q x y})))@-}
forallExistsImpl :: (a -> Bool) -> (a -> a -> Bool)
  -> (a -> (a,Proof -> Proof))
  -> (a -> (Proof -> (a,Proof)))
forallExistsImpl p q f x px 
  = case f x of 
      (y, pxToqxy) -> (y,pxToqxy px)

