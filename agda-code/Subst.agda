{-# OPTIONS --allow-unsolved-metas #-}
open import lib
open import bool-relations
open import VarInterface

module Subst(vi : VI) where

open VI vi
open import Tm vi 

----------------------------------------------------------------------
-- Definition of substitutions, helper functions
----------------------------------------------------------------------

-- a single substitution, requesting replacement of one variable by one term
Subst1 : Set
Subst1 = (V × Tm)

Subst : Set
Subst = 𝕃 Subst1

Renaming : Set
Renaming = 𝕃 (V × V)

-- would applying the given Subst1 to the given Tm avoid variable capture?
subst1ok : Subst1 → Tm → 𝔹
subst1ok (x , t) (var _) = tt
subst1ok (x , t) (t1 · t2) = subst1ok (x , t) t1 && subst1ok (x , t) t2
subst1ok (x , t) (ƛ y t') = x ≃ y || ~ (freeIn x t') || ((~ freeIn y t) && subst1ok (x , t) t')

substOk : Subst → Tm → 𝔹
substOk ss t = list-all (λ s → subst1ok s t) ss

-- find the first binding, if there is one, of the variable y in the substitution s
lookup : ∀{X : Set} → 𝕃 (V × X) → V → maybe X
lookup s y = maybe-map snd (find (λ p → y ≃ (fst p)) s)

rename-var : Renaming → V → V
rename-var r v with lookup r v
rename-var r v | nothing = v
rename-var r v | just v' = v'

renaming-dom : Renaming → 𝕃 V
renaming-dom = map fst

renaming-field : Renaming → 𝕃 V
renaming-field [] = []
renaming-field ((x , x') :: r) = x :: x' :: renaming-field r

renaming-ran : Renaming → 𝕃 V
renaming-ran = map snd

----------------------------------------------------------------------
-- Various functions for doing substitutions
----------------------------------------------------------------------

-- apply the given substitution simultaneously to the given term
subst : Subst → Tm → Tm
subst s (var y) with lookup s y
subst s (var y) | nothing = var y
subst s (var y) | just t = t
subst s (t1 · t2) = subst s t1 · subst s t2
subst s (ƛ x t) = ƛ x (subst (filter (λ p → ~ (fst p) ≃ x) s) t)

toSubst : Subst1 → Subst
toSubst s = [ s ]

subst1 : Subst1 → Tm → Tm
subst1 s t = subst (toSubst s) t

toSubst1 : V → Tm → Subst1
toSubst1 x t = (x , t)

[_/_]_ : Tm → V → Tm → Tm
[ t1 /  x ] t2 = subst1 (toSubst1 x t1) t2

<_↦_>_ : V → V → Tm → Tm
< x ↦ y > t = [ var y / x ] t

[_/_]ok_ : Tm → V → Tm → 𝔹
[ t2 / x ]ok t1 = subst1ok (toSubst1 x t2) t1

renameOk : V → V → Tm → 𝔹
renameOk x y t = subst1ok (toSubst1 x (var y)) t

renameOk· :
  ∀{x y : V}{t t' : Tm} →
   renameOk x y (t · t') ≡ tt →
   renameOk x y t ≡ tt ∧ renameOk x y t' ≡ tt

renameOk·{x}{y}{t}{t'} ro = &&-elim ro

----------------------------------------------------------------------
-- Theorems about substitution
----------------------------------------------------------------------

-- applying the empty substitution does not change the term
subst[] :
  ∀(t : Tm) →
   subst [] t ≡ t

subst[] (var x) = refl
subst[] (t · t₁) rewrite subst[] t | subst[] t₁ = refl
subst[] (ƛ x t) rewrite subst[] t = refl

-- substituting for a variable that does not occur free does not change the term
~free-subst :
  ∀{y}{t}{t'} →
   freeIn y t ≡ ff →
   [ t' / y ] t ≡ t

~free-subst {y} {var x} p rewrite ~≃-symm p = refl
~free-subst {y} {t · t₁} p with ||-≡-ff{freeIn y t} p 
~free-subst {y} {t · t₁}{t'} p | p1 , p2 rewrite ~free-subst{y}{t}{t'} p1 | ~free-subst{y}{t₁}{t'} p2 = refl
~free-subst {y} {ƛ x t} p with y ≃ x
~free-subst {y} {ƛ x t} p | tt rewrite subst[] t = refl
~free-subst {y} {ƛ x t}{t'} p | ff rewrite ~free-subst{y}{t}{t'} p = refl

{- renaming x to y and then y back to x does not change the term, as long as
   y is not free in the term and renaming x to y would not capture y -}
rename-undo :
  ∀{x y : V}{t : Tm} →
    freeIn y t ≡ ff →
    renameOk x y t ≡ tt → 
    < y ↦ x > < x ↦ y > t ≡ t

rename-undo {x} {y} {var x₁} fi ro with keep (x₁ ≃ x) 
rename-undo {x} {y} {var x₁} fi ro | tt , p rewrite p | ≃-refl {y} | ≃-≡ p = refl
rename-undo {x} {y} {var x₁} fi ro | ff , p rewrite p | ~≃-symm fi = refl
rename-undo {x} {y} {t1 · t2} fi ro with renameOk·{x}{y}{t1}{t2} ro | ||-≡-ff{freeIn y t1} fi
rename-undo {x} {y} {t1 · t2} fi ro | ro1 , ro2 | fi1 , fi2 rewrite rename-undo{x}{y}{t1} fi1 ro1 | rename-undo{x}{y}{t2} fi2 ro2 = refl
rename-undo {x} {y} {ƛ x₁ t} fi ro with ||-elim{x ≃ x₁} ro 
rename-undo {x} {y} {ƛ x₁ t} fi _ | inj₁ ro1 rewrite ro1 | subst[] t with y ≃ x₁ 
rename-undo {x} {y} {ƛ x₁ t} fi _ | inj₁ ro1 | tt rewrite subst[] t = refl
rename-undo {x} {y} {ƛ x₁ t} fi _ | inj₁ ro1 | ff rewrite ~free-subst{y}{t}{var x} fi = refl
rename-undo {x} {y} {ƛ x₁ t} fi _ | inj₂ ro1 with ||-elim{~ freeIn x t} ro1 
rename-undo {x} {y} {ƛ x₁ t} fi _ | inj₂ _ | inj₁ ro2 with y ≃ x₁ | x ≃ x₁
rename-undo {x} {y} {ƛ x₁ t} fi _ | inj₂ _ | inj₁ ro2 | tt | tt rewrite subst[] t | subst[] t = refl
rename-undo {x} {y} {ƛ x₁ t} fi _ | inj₂ _ | inj₁ ro2 | tt | ff rewrite ~free-subst{x}{t}{var y} (~-≡-tt ro2) | subst[] t = refl
rename-undo {x} {y} {ƛ x₁ t} fi _ | inj₂ _ | inj₁ ro2 | ff | tt rewrite subst[] t | ~free-subst{y}{t}{var x} fi = refl
rename-undo {x} {y} {ƛ x₁ t} fi _ | inj₂ _ | inj₁ ro2 | ff | ff rewrite ~free-subst{x}{t}{var y} (~-≡-tt ro2) | ~free-subst{y}{t}{var x} fi = refl
rename-undo {x} {y} {ƛ x₁ t} fi _ | inj₂ _ | inj₂ ro2 with &&-elim{~ x₁ ≃ y} ro2 
rename-undo {x} {y} {ƛ x₁ t} fi _ | inj₂ _ | inj₂ _ | ro2a , ro2b rewrite ~-≡-tt ro2a | ~≃-symm (~-≡-tt ro2a) with x ≃ x₁ 
rename-undo {x} {y} {ƛ x₁ t} fi _ | inj₂ _ | inj₂ _ | ro2a , ro2b | tt rewrite subst[] t | ~free-subst{y}{t}{var x} fi = refl
rename-undo {x} {y} {ƛ x₁ t} fi _ | inj₂ _ | inj₂ _ | ro2a , ro2b | ff rewrite rename-undo{x}{y}{t} fi ro2b = refl

-- if x is not free in t', then it is not free in the result of substituting t' for x
freeIn-subst :
  ∀ t' x t →
    freeIn x t' ≡ ff →
    freeIn x ([ t' / x ] t) ≡ ff

freeIn-subst t' x (var x₁) fi with keep (x₁ ≃ x) 
freeIn-subst t' x (var x₁) fi | tt , p rewrite p = fi
freeIn-subst t' x (var x₁) fi | ff , p rewrite p = ~≃-symm p
freeIn-subst t' x (t · t₁) fi rewrite freeIn-subst t' x t fi | freeIn-subst t' x t₁ fi = refl
freeIn-subst t' x (ƛ x₁ t) fi with x ≃ x₁
freeIn-subst t' x (ƛ x₁ t) fi | tt = refl
freeIn-subst t' x (ƛ x₁ t) fi | ff = freeIn-subst t' x t fi

-- renaming x to y where y is not free in t results in a term where it is safe to rename y back to x
renameOk-undo :
  ∀ x y t →
    freeIn y t ≡ ff →
    renameOk y x (< x ↦ y > t) ≡ tt

renameOk-undo x y (var x₁) fi with x₁ ≃ x
renameOk-undo x y (var x₁) fi | tt = refl
renameOk-undo x y (var x₁) fi | ff = refl
renameOk-undo x y (t · t₁) fi with ||-≡-ff{freeIn y t} fi 
renameOk-undo x y (t · t₁) fi | fi1 , fi2 rewrite renameOk-undo x y t fi1 | renameOk-undo x y t₁ fi2 = refl
renameOk-undo x y (ƛ x₁ t) fi with keep (x ≃ x₁) | keep (y ≃ x₁)
renameOk-undo x y (ƛ x₁ t) fi | tt , p | tt , q rewrite p | q | subst[] t = refl
renameOk-undo x y (ƛ x₁ t) fi | tt , p | ff , q rewrite p | q | subst[] t rewrite fi = refl
renameOk-undo x y (ƛ x₁ t) fi | ff , p | tt , q rewrite p | q | ~≃-symm p = refl
renameOk-undo x y (ƛ x₁ t) fi | ff , p | ff , q rewrite p | q | ~≃-symm p rewrite renameOk-undo x y t fi = ||-tt (~ freeIn y (< x ↦ y > t))


[/]ok-subst : ∀{t1 t2 t : Tm}{x y : V} → 
               ([ t / x ]ok t1) ≡ tt →                
               ([ t / x ]ok t2) ≡ tt →
               ([ t / x ]ok [ t2 / y ] t1) ≡ tt 
[/]ok-subst {var z}{t2}{t}{x}{y} p1 p2 with y ≃ z | z ≃ y
[/]ok-subst {var z}{t2}{t}{x}{y} p1 p2 | tt | tt = p2
[/]ok-subst {var z}{t2}{t}{x}{y} p1 p2 | ff | tt = p2
[/]ok-subst {var z}{t2}{t}{x}{y} p1 p2 | tt | ff = refl
[/]ok-subst {var z}{t2}{t}{x}{y} p1 p2 | ff | ff = refl
[/]ok-subst {t1a · t1b}{t2}{t}{x}{y} p1 p2 =
  &&-intro{[ t / x ]ok [ t2 / y ] t1a}
    ([/]ok-subst{t1a}{t2}{t}{x}{y} (&&-elim1 p1) p2)
    ([/]ok-subst{t1b}{t2}{t}{x}{y} (&&-elim2 p1) p2)
[/]ok-subst {ƛ z t1}{t2}{t}{x}{y} p1 p2 with y ≃ z | x ≃ z
[/]ok-subst {ƛ z t1}{t2}{t}{x}{y} p1 p2 | tt | tt = refl 
[/]ok-subst {ƛ z t1}{t2}{t}{x}{y} p1 p2 | ff | tt = refl -- rewrite [/]ok-subst {t1}{t2}{t}{x}{y} {!p1!} p2 = {!!}
[/]ok-subst {ƛ z t1}{t2}{t}{x}{y} p1 p2 | tt | ff rewrite subst[] t1 = p1
[/]ok-subst {ƛ z t1}{t2}{t}{x}{y} p1 p2 | ff | ff with ||-elim{~ freeIn x t1} p1
[/]ok-subst {ƛ z t1}{t2}{t}{x}{y} p1 p2 | ff | ff | inj₁ q = {!!}
[/]ok-subst {ƛ z t1}{t2}{t}{x}{y} p1 p2 | ff | ff | inj₂ q = {!!}