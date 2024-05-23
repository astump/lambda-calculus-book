open import lib
open import relations 
open import VarInterface

module Tau(vi : VI) where

open VI vi
open import Tm vi

data τ(r : Rel Tm) : Rel Tm where
 τ-base : ∀ {t1 t2 : Tm} → r t1 t2 → τ r t1 t2
 τ-app1 : ∀ {t1 t1' t2 : Tm} → τ r t1 t1' → τ r (t1 · t2) (t1' · t2)
 τ-app2 : ∀ {t1 t2 t2' : Tm} → τ r t2 t2' → τ r (t1 · t2) (t1 · t2')
 τ-lam : ∀{v : V}{t t' : Tm} → τ r t t' → τ r (ƛ v t) (ƛ v t')

τ-symm : ∀{r : Rel Tm} → symmetric r → symmetric (τ r)
τ-symm u (τ-base x) = τ-base (u x)
τ-symm u (τ-app1 p) = τ-app1 (τ-symm u p)
τ-symm u (τ-app2 p) = τ-app2 (τ-symm u p)
τ-symm u (τ-lam p) = τ-lam (τ-symm u p)