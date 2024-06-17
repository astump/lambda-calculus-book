open import lib
open import VarInterface

module Tm(vi : VI) where

open VI vi

data Tm : Set where
  var : (x : V) → Tm
  _·_ : (t : Tm) → (t' : Tm) → Tm
  ƛ : (x : V) → (t : Tm) → Tm

infixl 10 _·_ 

-- is the given variable free in the given term
freeIn : V → Tm → Set
freeIn x (var y) = x ≃ y ≡ tt
freeIn x (t · t') = (freeIn x t) ∨ (freeIn x t')
freeIn x (ƛ y t) = x ≃ y ≡ ff ∧ freeIn x t

-- is the given variable free in the given term
boundIn : V → Tm → Set
boundIn x (var y) = ⊥
boundIn x (t · t') = (boundIn x t) ∨ (boundIn x t')
boundIn x (ƛ y t) = x ≃ y ≡ tt ∨ boundIn x t

bv-apart : Tm → Tm → Set
bv-apart t2 t1 = ∀ (x : V) → freeIn x t2 → ¬ boundIn x t1

bv-apart-app : ∀{t2 t1a t1b : Tm} →
                bv-apart t2 (t1a · t1b) →
                bv-apart t2 t1a ∧ bv-apart t2 t1b
bv-apart-app{t2}{t1a}{t1b} a = (λ x u b → a x u (inj₁ b)) , λ x u b → a x u (inj₂ b)

bv-apart-app' : ∀{t2 t1a t1b : Tm} →
                bv-apart t2 t1a →
                bv-apart t2 t1b → 
                bv-apart t2 (t1a · t1b)
bv-apart-app'{t2}{t1a}{t1b} a1 a2 x u (inj₁ b) = a1 x u b
bv-apart-app'{t2}{t1a}{t1b} a1 a2 x u (inj₂ b) = a2 x u b

bv-apart-lam : ∀{t2 : Tm}{x : V}{t1 : Tm} →
                bv-apart t2 (ƛ x t1) →
                ¬ freeIn x t2 ∧ bv-apart t2 t1
bv-apart-lam{t2}{x}{t1} u = (λ f → u x f (inj₁ (≃-refl {x}))) , λ y f b → u y f (inj₂ b)

¬freeIn-app : ∀{x : V}{t t' : Tm} →
               ¬ freeIn x (t · t') →
               ¬ (freeIn x t) ∧ ¬ (freeIn x t')
¬freeIn-app{x}{t}{t'} nf = (λ f → nf (inj₁ f)) , (λ f → nf (inj₂ f))

¬freeIn-lam : ∀{x y : V}{t : Tm} →
               ¬ freeIn x (ƛ y t) →
               x ≃ y ≡ tt ∨ (x ≃ y ≡ ff ∧ ¬ freeIn x t)
¬freeIn-lam{x}{y}{t} nf with x ≃ y
¬freeIn-lam{x}{y}{t} nf | tt = inj₁ refl
¬freeIn-lam{x}{y}{t} nf | ff = inj₂ (refl , (λ f → nf (refl , f)))

fv : Tm → 𝕃 V
fv (var x) = [ x ]
fv (t1 · t2) = fv t1 ++ fv t2
fv (ƛ x t) = remove _≃_ x (fv t)