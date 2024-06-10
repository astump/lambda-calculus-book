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
   substOk s t1 ∧
   t' ≡ subst s t1
β _ _ = ⊥

↝β : Rel Tm
↝β = τ β

↝αβ : Rel Tm
↝αβ = ↝α ∪ ↝β

↝ : Rel Tm
↝ = =α ∘ ↝β ∘ =α

β-freeIn : ∀{x : V}{t t' : Tm} →
            freeIn x t' → 
            t ⟨ β ⟩ t' →
            freeIn x t
β-freeIn{x}{(ƛ y t1) · t2} u ((b , triv) , refl) with keep (x ≃ y)
β-freeIn{x}{(ƛ y t1) · t2} u ((b , triv) , refl) | tt , e rewrite ≃-≡ e = inj₂ (freeIn-subst-same{t2}{y}{t1} u)
β-freeIn{x}{(ƛ y t1) · t2} u ((b , triv) , refl) | ff , e with freeIn-subst{x}{t2}{y}{t1} u
β-freeIn{x}{(ƛ y t1) · t2} u ((b , triv) , refl) | ff , e | inj₁ p = inj₁ (e , p)
β-freeIn{x}{(ƛ y t1) · t2} u ((b , triv) , refl) | ff , e | inj₂ (p , q) = inj₂ p

↝β-freeIn : ∀{x : V}{t t' : Tm} →
            freeIn x t' → 
            t ⟨ ↝β ⟩ t' →
            freeIn x t
↝β-freeIn f (τ-base d) = β-freeIn f d
↝β-freeIn (inj₁ f) (τ-app1 d) = inj₁ (↝β-freeIn f d)
↝β-freeIn (inj₂ f) (τ-app1 d) = inj₂ f
↝β-freeIn (inj₁ f) (τ-app2 d) = inj₁ f
↝β-freeIn (inj₂ f) (τ-app2 d) = inj₂ (↝β-freeIn f d)
↝β-freeIn{x} f (τ-lam{v} d) with x ≃ v
↝β-freeIn{x} (() , _) (τ-lam{v} d) | tt 
↝β-freeIn{x} (_ , f) (τ-lam{v} d) | ff = refl , ↝β-freeIn f d

↝β⋆-freeIn : ∀{x : V}{t t' : Tm} →
            freeIn x t' → 
            t ⟨ ↝β ⋆ ⟩ t' →
            freeIn x t
↝β⋆-freeIn f ⋆refl = f
↝β⋆-freeIn f (⋆base d) = ↝β-freeIn f d
↝β⋆-freeIn f (d1 ⋆trans d2) = ↝β⋆-freeIn (↝β⋆-freeIn f d2) d1

β-boundIn : ∀{x : V}{t t' : Tm} →
            boundIn x t' → 
            t ⟨ β ⟩ t' →
            boundIn x t
β-boundIn{x}{(ƛ y t1) · t2} u ((b , triv) , refl) with keep (x ≃ y)
β-boundIn{x}{(ƛ y t1) · t2} u ((b , triv) , refl) | tt , e rewrite ≃-≡ e = inj₁ (inj₁ ≃-refl)
β-boundIn{x}{(ƛ y t1) · t2} u ((b , triv) , refl) | ff , e with boundIn-subst{x}{t2}{y}{t1} u
β-boundIn{x}{(ƛ y t1) · t2} u ((b , triv) , refl) | ff , e | inj₁ p = inj₁ (inj₂ p)
β-boundIn{x}{(ƛ y t1) · t2} u ((b , triv) , refl) | ff , e | inj₂ (p , q) = inj₂ p

↝β-boundIn : ∀{x : V}{t t' : Tm} →
              boundIn x t' → 
              t ⟨ ↝β ⟩ t' →
              boundIn x t
↝β-boundIn f (τ-base d) = β-boundIn f d
↝β-boundIn (inj₁ f) (τ-app1 d) = inj₁ (↝β-boundIn f d)
↝β-boundIn (inj₂ f) (τ-app1 d) = inj₂ f
↝β-boundIn (inj₁ f) (τ-app2 d) = inj₁ f
↝β-boundIn (inj₂ f) (τ-app2 d) = inj₂ (↝β-boundIn f d)
↝β-boundIn{x} f (τ-lam{v} d) with x ≃ v
↝β-boundIn{x} f (τ-lam{v} d) | tt = inj₁ refl
↝β-boundIn{x} (inj₁ ()) (τ-lam{v} d) | ff
↝β-boundIn{x} (inj₂ f) (τ-lam{v} d) | ff = inj₂ (↝β-boundIn f d)

↝β⋆-boundIn : ∀{x : V}{t t' : Tm} →
            boundIn x t' → 
            t ⟨ ↝β ⋆ ⟩ t' →
            boundIn x t
↝β⋆-boundIn f ⋆refl = f
↝β⋆-boundIn f (⋆base d) = ↝β-boundIn f d
↝β⋆-boundIn f (d1 ⋆trans d2) = ↝β⋆-boundIn (↝β⋆-boundIn f d2) d1
