{-# OPTIONS --allow-unsolved-metas #-}
{- definition of parallel reduction, for proof of confluence.

   The definition here builds in alpha-equivalence for the lambda case. -}
open import lib
open import relations
open import diamond
open import VarInterface

module Parallel(vi : VI) where

open VI vi
open import Tm vi
open import Subst vi
open import Beta vi
open import Alpha vi 
open import Tau vi 

data ⇒ : Tm → Tm → Set where
  ⇒var : ∀{v : V} →
          var v ⟨ ⇒ ⟩ var v
  ⇒app : ∀{t1 t1' t2 t2' c : Tm} → 
          t1 ⟨ ⇒ ⟩ t1' →
          t2 ⟨ ⇒ ⟩ t2' →
          (t1' · t2') ⟨ 1r ∪ β ⟩ c →
          (t1 · t2) ⟨ ⇒ ⟩ c
  ⇒lam : ∀{x : V}{t1 t1' c : Tm} →
           t1 ⟨ ⇒ ⟩ t1' →
           (ƛ x t1') ⟨ 1r ∪ α ⟩ c →
           (ƛ x t1) ⟨ ⇒ ⟩ c


-- parallel reduction is reflexive
⇒refl : reflexive ⇒ 
⇒refl {var x} = ⇒var
⇒refl {t · t₁} = ⇒app ⇒refl ⇒refl (inj₁ refl)
⇒refl {ƛ x t} = ⇒lam ⇒refl (inj₁ refl)

-- bare α is included in parallel reduction
α-⇒ : α ⊆ ⇒
α-⇒{ƛ x t1}{ƛ y t2} p = ⇒lam ⇒refl (inj₂ p)

-- α-reduction is included in parallel reduction
↝α-⇒ : ↝α ⊆ ⇒
↝α-⇒ (τ-base x) = α-⇒ x
↝α-⇒ (τ-app1 x) = ⇒app (↝α-⇒ x) ⇒refl (inj₁ refl)
↝α-⇒ (τ-app2 x) = ⇒app ⇒refl (↝α-⇒ x) (inj₁ refl)
↝α-⇒ (τ-lam x) = ⇒lam (↝α-⇒ x) (inj₁ refl)

↝β-⇒ : ↝β ⊆ ⇒
↝β-⇒ {(ƛ x t1) · t2}{a'} (τ-base p) = ⇒app ⇒refl ⇒refl (inj₂ p)
↝β-⇒ (τ-app1 x) = ⇒app (↝β-⇒ x) ⇒refl (inj₁ refl)
↝β-⇒ (τ-app2 x) = ⇒app ⇒refl (↝β-⇒ x) (inj₁ refl)
↝β-⇒ (τ-lam x) = ⇒lam (↝β-⇒ x) (inj₁ refl)

↝αβ-⇒ : ↝αβ ⊆ ⇒
↝αβ-⇒ (inj₁ p) = ↝α-⇒ p
↝αβ-⇒ (inj₂ p) = ↝β-⇒ p

⇒-↝αβ⋆ : ⇒ ⊆ ↝αβ ⋆
⇒-↝αβ⋆ ⇒var = ⋆refl
⇒-↝αβ⋆ (⇒app x1 x2 b) with (↝αβ-app1⋆ (⇒-↝αβ⋆ x1)) ⋆trans (↝αβ-app2⋆ (⇒-↝αβ⋆ x2))
⇒-↝αβ⋆ (⇒app x1 x2 (inj₁ refl)) | p = p
⇒-↝αβ⋆ (⇒app x1 x2 (inj₂ b)) | p = p ⋆trans (⋆base (inj₂ (τ-base b)))
⇒-↝αβ⋆ (⇒lam{x} p b) with ↝αβ-lam⋆{x} (⇒-↝αβ⋆ p)
⇒-↝αβ⋆ (⇒lam{x} p (inj₁ refl)) | q = q
⇒-↝αβ⋆ (⇒lam{x} p (inj₂ b)) | q = q ⋆trans (⋆base (inj₁ (τ-base b)))

