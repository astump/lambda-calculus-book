{- concrete examples of beta reductions.  Writing the derivations by hand is not too fun. -}

open import lib
open import VarInterface

module BetaExamples where

open import Tm VI-ℕ
open import Alpha VI-ℕ
open import Beta VI-ℕ
open import Tau VI-ℕ

id : Tm
id = ƛ 0 (var 0)

r1 : (id · id) ⟨ β ⟩ id
r1 = refl , refl

r1a : (id · id) ⟨ ↝β ⟩ id
r1a = τ-base r1

r1b : (id · id) ⟨ ↝β ⋆ ⟩ id
r1b = ⋆base r1a

two : Tm
two = ƛ 0 (ƛ 1 (var 0 · (var 0 · var 1)))

r2 : (two · id) ⟨ ↝β ⋆ ⟩ (ƛ 1 (var 1))
r2 = (⋆base (τ-base (refl , refl))) ⋆trans (⋆base (τ-lam (τ-base (refl , refl)))) ⋆trans (⋆base (τ-lam (τ-base (refl , refl))))

{- here is an example of alpha equivalence that cannot be proved just by alpha -}
a1 : ƛ 0 (ƛ 1 (var 0 · var 1)) ⟨ =α ⟩ ƛ 1 (ƛ 0 (var 1 · var 0))
a1 = d1 ⋆trans d2 ⋆trans d3
  where d1 : ƛ 0 (ƛ 1 (var 0 · var 1)) ⟨ =α ⟩ ƛ 2 (ƛ 1 (var 2 · var 1))
        d1 = ⋆base (τ-base (refl , refl , refl , refl))

        d2 : ƛ 2 (ƛ 1 (var 2 · var 1)) ⟨ =α ⟩ ƛ 2 (ƛ 0 (var 2 · var 0))
        d2 = ⋆base (τ-lam (τ-base (refl , refl , refl , refl)))

        d3 : ƛ 2 (ƛ 0 (var 2 · var 0)) ⟨ =α ⟩ ƛ 1 (ƛ 0 (var 1 · var 0))
        d3 = ⋆base (τ-base (refl , refl , refl , refl))
