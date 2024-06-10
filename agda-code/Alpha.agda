open import lib
open import relations as R
open import VarInterface

module Alpha(vi : VI) where

open VI vi
open import Tm vi
open import Subst vi
open import Tau vi

----------------------------------------------------------------------
-- The bare α relation, relating one λ-abstraction to a renamed 
-- version
----------------------------------------------------------------------

α : Rel Tm
α (ƛ x t1) (ƛ y t2) =
   renameOk x y t1 ∧
   ¬ freeIn y t1 ∧
   x ≃ y ≡ ff ∧         -- don't allow trivial renamings
   t2 ≡ < x ↦ y > t1
α _ _ = ⊥

↝α : Rel Tm
↝α = τ α

=α : Rel Tm
=α = ↝α ⋆

----------------------------------------------------------------------
-- Theorems about α
----------------------------------------------------------------------

{-

α-symm : R.symmetric α
α-symm {ƛ x t1} {ƛ y t2} (s , f , xy , refl) = renameOk-undo x y t1 f , freeIn-subst (var y) x t1 xy , ~≃-symm xy , sym (rename-undo f s) 

↝α-symm : R.symmetric ↝α
↝α-symm = τ-symm α-symm

=α-symm : R.symmetric =α
=α-symm = ⋆symm ↝α-symm

=α-refl : R.reflexive =α
=α-refl = ⋆refl

=α-trans : R.transitive =α
=α-trans = _⋆trans_

=α-equiv : R.equivalence =α
=α-equiv = (=α-refl , =α-trans) , =α-symm

-}