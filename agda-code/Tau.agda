open import lib
open import relations 
open import VarInterface

module Tau(vi : VI) where

open VI vi
open import Tm vi

data τ(r : Rel Tm) : Rel Tm where
 τ-base : ∀ {t1 t2 : Tm} → t1 ⟨ r ⟩ t2 → t1 ⟨ τ r ⟩ t2
 τ-app1 : ∀ {t1 t1' t2 : Tm} → t1 ⟨ τ r ⟩ t1' → (t1 · t2) ⟨ τ r ⟩ (t1' · t2)
 τ-app2 : ∀ {t1 t2 t2' : Tm} → t2 ⟨ τ r ⟩ t2' → (t1 · t2) ⟨ τ r ⟩ (t1 · t2')
 τ-lam : ∀{v : V}{t t' : Tm} → t ⟨ τ r ⟩ t' → (ƛ v t) ⟨ τ r ⟩ (ƛ v t')

τ-symm : ∀{r : Rel Tm} → symmetric r → symmetric (τ r)
τ-symm u (τ-base x) = τ-base (u x)
τ-symm u (τ-app1 p) = τ-app1 (τ-symm u p)
τ-symm u (τ-app2 p) = τ-app2 (τ-symm u p)
τ-symm u (τ-lam p) = τ-lam (τ-symm u p)

⋆app1 : ∀{t1 t1' t2 : Tm}{r : Rel Tm} →
         t1 ⟨ (τ r) ⋆ ⟩ t1' →
         (t1 · t2) ⟨ (τ r) ⋆ ⟩ (t1' · t2)
⋆app1 ⋆refl = ⋆refl
⋆app1 (⋆base p) = ⋆base (τ-app1 p)
⋆app1 (p1 ⋆trans p2) = (⋆app1 p1) ⋆trans (⋆app1 p2)

⋆app2 : ∀{t1 t2 t2' : Tm}{r : Rel Tm} →
         t2 ⟨ (τ r) ⋆ ⟩ t2' →
         (t1 · t2) ⟨ (τ r) ⋆ ⟩ (t1 · t2')
⋆app2 ⋆refl = ⋆refl
⋆app2 (⋆base p) = ⋆base (τ-app2 p)
⋆app2 (p1 ⋆trans p2) = (⋆app2 p1) ⋆trans (⋆app2 p2)

⋆lam : ∀{v : V}{t t' : Tm}{r : Rel Tm} →
         t ⟨ (τ r) ⋆ ⟩ t' →
         (ƛ v t) ⟨ (τ r) ⋆ ⟩ (ƛ v t')
⋆lam ⋆refl = ⋆refl
⋆lam (⋆base p) = ⋆base (τ-lam p)
⋆lam (p1 ⋆trans p2) = (⋆lam p1) ⋆trans (⋆lam p2)
