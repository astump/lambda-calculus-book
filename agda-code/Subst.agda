open import lib
open import bool-relations
open import VarInterface

module Subst(vi : VI) where

open VI vi
open import Tm vi
open import FreeVars vi 

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

subst-ran : Subst → 𝕃 Tm
subst-ran = map snd

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

{- some annoying lemmas I did not attempt to carry out in place below -}
list-all-fv-lem : ∀(x y z : V) → 
                  x ≃ y ≡ ff → ~ (y ≃ z) ≡ ff → ~ (z ≃ x) || ff ≡ tt
list-all-fv-lem x y z u v with keep (y ≃ z) 
list-all-fv-lem x y z u v | ff , p rewrite p with v 
list-all-fv-lem x y z u v | ff , p | ()
list-all-fv-lem x y z u v | tt , p rewrite ≃-≡ p | ~≃-symm u = refl

list-all-fv-lem2 : ∀{x : V}(a : V) → ~ (a ≃ x) ≡ tt → ~ (a ≃ x) || ff ≡ tt
list-all-fv-lem2{x} a u with a ≃ x 
list-all-fv-lem2{x} a u | tt with u
list-all-fv-lem2{x} a u | tt | ()
list-all-fv-lem2{x} a u | ff = refl

list-all-fv-lem3 : ∀{x : V}(a : V) → ~ (a ≃ x) || ff ≡ tt → ~ (a ≃ x) ≡ tt
list-all-fv-lem3{x} a u with a ≃ x 
list-all-fv-lem3{x} a u | tt with u
list-all-fv-lem3{x} a u | tt | ()
list-all-fv-lem3{x} a u | ff = refl

subst1ok-apart-lem : {x : V}(a : V) → ~ ((a ≃ x) || ff) ≡ tt → ~ (a ≃ x) ≡ tt
subst1ok-apart-lem{x} a u with a ≃ x
subst1ok-apart-lem a u | tt with u
subst1ok-apart-lem a u | tt | ()
subst1ok-apart-lem a u | ff = refl

{- if x is different from all the free variables of t, then x is not free in t -}
list-all-fv : ∀{x : V}{t : Tm} → 
  list-all (λ y → ~ (y ≃ x)) (fv t) ≡ tt →
  freeIn x t ≡ ff
list-all-fv {x} {var y} p with keep (y ≃ x) 
list-all-fv {x} {var y} p | tt , r rewrite r with p
list-all-fv {x} {var y} p | tt , r | ()
list-all-fv {x} {var y} p | ff , r rewrite ~≃-symm r = refl
list-all-fv {x} {t1 · t2} p rewrite list-all-append (λ y → ~ (y ≃ x)) (fv t1) (fv t2)
  with &&-elim {list-all (λ y → ~ (y ≃ x)) (fv t1)} p 
list-all-fv {x} {t1 · t2} p | p1 , p2 rewrite list-all-fv{x}{t1} p1 | list-all-fv{x}{t2} p2 = refl
list-all-fv {x} {ƛ y t} p with keep (x ≃ y)
list-all-fv {x} {ƛ y t} p | tt , q rewrite q = refl
list-all-fv {x} {ƛ y t} p | ff , q rewrite q
  with list-all-filter (fv t) (λ z u → list-all-fv-lem x y z q u)
         (list-all-sub (filter (λ z → ~ (y ≃ z)) (fv t)) list-all-fv-lem2  p) 
list-all-fv {x} {ƛ y t} p | ff , q | r =
  list-all-fv{x}{t} ((list-all-sub (fv t) list-all-fv-lem3 r))

{- if the list of free variables of t2 is disjoint from the list of bound variables of t1,
   then t2 can be substituted into t1 without risk of capture -}
subst1ok-apart : ∀{t2 : Tm}{x : V}{t1 : Tm} →
                  bv-apart t2 t1 ≡ tt → 
                  [ t2 / x ]ok t1 ≡ tt
subst1ok-apart{t1 = var x} u = refl
subst1ok-apart{t2}{x}{t1a · t1b} u with disjoint-++{l1 = fv t2}{bv t1a}{bv t1b} u
subst1ok-apart{t2}{x}{t1a · t1b} _ | u1 , u2
  rewrite subst1ok-apart{t2}{x}{t1 = t1a} u1 | subst1ok-apart{t2}{x}{t1 = t1b} u2 = refl
subst1ok-apart{t2}{y}{t1 = ƛ x t1} u with disjoint-++{l1 = fv t2}{l2a = [ x ]}{l2b = bv t1} u
subst1ok-apart{t2}{y}{t1 = ƛ x t1} u | u1 , u2 = 
  ||-intro2{y ≃ x}
  (||-intro2 {~ freeIn y t1}
  (&&-intro {~ freeIn x t2}
     (cong ~_ (list-all-fv{x}{t2} (list-all-sub (fv t2) subst1ok-apart-lem u1)))
     (subst1ok-apart {t2} {y} {t1} (snd (disjoint-++{l1 = fv t2}{[ x ]}{bv t1} u)))))