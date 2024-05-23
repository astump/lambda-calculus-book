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

