open import lib
open import bool-relations as B
open import relations as R
open import VarInterface

module Alpha(vi : VI) where

open VI vi
open import Tm vi
open import Subst vi

----------------------------------------------------------------------
-- The bare α relation, relating one λ-abstraction to a renamed 
-- version
----------------------------------------------------------------------

_α_ : Rel Tm
(ƛ x t1) α (ƛ y t2) =
   renameOk x y t1 ≡ tt ∧
   freeIn y t1 ≡ ff ∧
   x ≃ y ≡ ff ∧         -- don't allow trivial renamings
   t2 ≡ < x ↦ y > t1
_ α _ = ⊥

----------------------------------------------------------------------
-- Theorems about α
----------------------------------------------------------------------

α-symm : R.symmetric _α_
α-symm {ƛ x t1} {ƛ y t2} (s , f , xy , refl) = renameOk-undo x y t1 f , freeIn-subst (var y) x t1 xy , ~≃-symm xy , sym (rename-undo f s) 
