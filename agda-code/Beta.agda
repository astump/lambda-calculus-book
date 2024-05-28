open import lib
open import VarInterface

module Beta(vi : VI) where

open VI vi
open import Tm vi
open import Subst vi
open import Tau vi
open import Alpha vi

β : Rel Tm
β ((ƛ x t1) · t2) t' =
 let s = [ (x , t2) ] in
   substOk s t1 ≡ tt ∧
   t' ≡ subst s t1
β _ _ = ⊥

↝β : Rel Tm
↝β = τ β

↝αβ : Rel Tm
↝αβ = ↝α ∪ ↝β

↝ : Rel Tm
↝ = =α ∘ ↝β ∘ =α

↝αβ-app1⋆ : ∀{t1 t1' t2 : Tm} →
             t1 ⟨ ↝αβ ⋆ ⟩ t1' →
             (t1 · t2) ⟨ ↝αβ ⋆ ⟩ (t1' · t2)
↝αβ-app1⋆ ⋆refl = ⋆refl
↝αβ-app1⋆ (⋆base (inj₁ p)) = ⋆base (inj₁ (τ-app1 p))
↝αβ-app1⋆ (⋆base (inj₂ p)) = ⋆base (inj₂ (τ-app1 p))
↝αβ-app1⋆ (p1 ⋆trans p2) = (↝αβ-app1⋆ p1) ⋆trans (↝αβ-app1⋆ p2)

↝αβ-app2⋆ : ∀{t1 t2 t2' : Tm} →
             t2 ⟨ ↝αβ ⋆ ⟩ t2' →
             (t1 · t2) ⟨ ↝αβ ⋆ ⟩ (t1 · t2')
↝αβ-app2⋆ ⋆refl = ⋆refl
↝αβ-app2⋆ (⋆base (inj₁ p)) = ⋆base (inj₁ (τ-app2 p))
↝αβ-app2⋆ (⋆base (inj₂ p)) = ⋆base (inj₂ (τ-app2 p))
↝αβ-app2⋆ (p1 ⋆trans p2) = (↝αβ-app2⋆ p1) ⋆trans (↝αβ-app2⋆ p2)

↝αβ-lam⋆ : ∀{v : V}{t t' : Tm} →
            t ⟨ ↝αβ ⋆ ⟩ t' →
            (ƛ v t) ⟨ ↝αβ ⋆ ⟩ (ƛ v t')
↝αβ-lam⋆ ⋆refl = ⋆refl
↝αβ-lam⋆ (⋆base (inj₁ p)) = ⋆base (inj₁ (τ-lam p))
↝αβ-lam⋆ (⋆base (inj₂ p)) = ⋆base (inj₂ (τ-lam p))
↝αβ-lam⋆ (p1 ⋆trans p2) = (↝αβ-lam⋆ p1) ⋆trans (↝αβ-lam⋆ p2) 
