open import lib
open import bool-relations as B
open import relations as R
open import VarInterface

module Beta(vi : VI) where

open VI vi
open import Tm vi
open import Subst vi

β : Rel Tm
β ((ƛ x t1) · t2) t' =
 let s = [ (x , t2) ] in
   substOk s t1 ≡ tt ∧
   t' ≡ subst s t1
β _ _ = ⊥


