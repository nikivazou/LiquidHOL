import Language.Haskell.Liquid.ProofCombinators

{-@ LIQUID "--higherorder" @-}

{-@ natinduction :: p:(Int-> Bool) -> PAnd {v:Proof | p 0} (n:Int -> {v:Proof | p (n-1)} -> {v:Proof | p n})
                 -> n:Nat -> {v:Proof | p n}  @-}
natinduction :: (Int-> Bool) -> PAnd Proof (Int -> Proof -> Proof)-> Int -> Proof 
natinduction p (PAnd p0 pi) n  
  | n == 0    = p0 
  | otherwise = pi n (natinduction p (PAnd p0 pi) (n-1))
