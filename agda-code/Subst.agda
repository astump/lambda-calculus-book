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
subst1ok : Subst1 → Tm → Set
subst1ok (x , t) (var _) = ⊤
subst1ok (x , t) (t1 · t2) = subst1ok (x , t) t1 ∧ subst1ok (x , t) t2
subst1ok (x , t) (ƛ y t') = x ≃ y ≡ tt ∨ ¬ (freeIn x t') ∨ (¬ freeIn y t ∧ subst1ok (x , t) t')

substOk : Subst → Tm → Set
substOk [] t = ⊤
substOk (s :: ss) t = subst1ok s t ∧ substOk ss t

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

subst-drop : ∀{A : Set} → V → 𝕃 (V × A) → 𝕃 (V × A)
subst-drop x = filter (λ p → ~ (fst p) ≃ x)

-- apply the given substitution simultaneously to the given term
subst : Subst → Tm → Tm
subst s (var y) with lookup s y
subst s (var y) | nothing = var y
subst s (var y) | just t = t
subst s (t1 · t2) = subst s t1 · subst s t2
subst s (ƛ x t) = ƛ x (subst (subst-drop x s) t)

renaming-to-subst : Renaming → Subst
renaming-to-subst = map (snd-map var)

rename : Renaming → Tm → Tm
rename r = subst (renaming-to-subst r)

renameOk : Renaming → Tm → Set
renameOk r t = substOk (renaming-to-subst r) t

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

[_/_]ok_ : Tm → V → Tm → Set
[ t2 / x ]ok t1 = subst1ok (toSubst1 x t2) t1

rename1Ok : V → V → Tm → Set
rename1Ok x y t = subst1ok (toSubst1 x (var y)) t

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

freeIn-subst : ∀{x : V}{t2 : Tm}{y : V}{t1 : Tm} →
                freeIn x ([ t2 / y ] t1) →
                freeIn x t1 ∨ (freeIn x t2 ∧ freeIn y t1)
freeIn-subst {x} {t2} {y} {var z} u with keep (z ≃ y) 
freeIn-subst {x} {t2} {y} {var z} u | tt , p rewrite p | ≃-sym p = inj₂ (u , refl)
freeIn-subst {x} {t2} {y} {var z} u | ff , p rewrite p = inj₁ u
freeIn-subst {x} {t2} {y} {t1a · t1b} (inj₁ u) with freeIn-subst{x}{t2}{y}{t1a} u
freeIn-subst {x} {t2} {y} {t1a · t1b} (inj₁ u) | inj₁ v = inj₁ (inj₁ v)
freeIn-subst {x} {t2} {y} {t1a · t1b} (inj₁ u) | inj₂ (v1 , v2) = inj₂ (v1 , (inj₁ v2))
freeIn-subst {x} {t2} {y} {t1a · t1b} (inj₂ u) with freeIn-subst{x}{t2}{y}{t1b} u
freeIn-subst {x} {t2} {y} {t1a · t1b} (inj₂ u) | inj₁ v = inj₁ (inj₂ v)
freeIn-subst {x} {t2} {y} {t1a · t1b} (inj₂ u) | inj₂ (v1 , v2) = inj₂ (v1 , inj₂ v2)
freeIn-subst {x} {t2} {y} {ƛ z t1} u with y ≃ z
freeIn-subst {x} {t2} {y} {ƛ z t1} (u1 , u2) | tt rewrite subst[] t1 = inj₁ (u1 , u2)
freeIn-subst {x} {t2} {y} {ƛ z t1} (u1 , u2) | ff with freeIn-subst{x}{t2}{y}{t1} u2
freeIn-subst {x} {t2} {y} {ƛ z t1} (u1 , u2) | ff | inj₁ q = inj₁ (u1 , q)
freeIn-subst {x} {t2} {y} {ƛ z t1} (u1 , u2) | ff | inj₂ (q1 , q2) = inj₂ (q1 , refl , q2)

boundIn-subst : ∀{x : V}{t2 : Tm}{y : V}{t1 : Tm} →
                boundIn x ([ t2 / y ] t1) →
                boundIn x t1 ∨ (boundIn x t2 ∧ freeIn y t1)
boundIn-subst {x} {t2} {y} {var z} u with keep (z ≃ y) 
boundIn-subst {x} {t2} {y} {var z} u | tt , p rewrite p | ≃-sym p = inj₂ (u , refl)
boundIn-subst {x} {t2} {y} {var z} u | ff , p rewrite p = inj₁ u
boundIn-subst {x} {t2} {y} {t1a · t1b} (inj₁ u) with boundIn-subst{x}{t2}{y}{t1a} u
boundIn-subst {x} {t2} {y} {t1a · t1b} (inj₁ u) | inj₁ v = inj₁ (inj₁ v)
boundIn-subst {x} {t2} {y} {t1a · t1b} (inj₁ u) | inj₂ (v1 , v2) = inj₂ (v1 , (inj₁ v2))
boundIn-subst {x} {t2} {y} {t1a · t1b} (inj₂ u) with boundIn-subst{x}{t2}{y}{t1b} u
boundIn-subst {x} {t2} {y} {t1a · t1b} (inj₂ u) | inj₁ v = inj₁ (inj₂ v)
boundIn-subst {x} {t2} {y} {t1a · t1b} (inj₂ u) | inj₂ (v1 , v2) = inj₂ (v1 , inj₂ v2)
boundIn-subst {x} {t2} {y} {ƛ z t1} u with y ≃ z
boundIn-subst {x} {t2} {y} {ƛ z t1} u | tt rewrite subst[] t1 = inj₁ u
boundIn-subst {x} {t2} {y} {ƛ z t1} (inj₁ u) | ff = inj₁ (inj₁ u)
boundIn-subst {x} {t2} {y} {ƛ z t1} (inj₂ u) | ff with boundIn-subst{x}{t2}{y}{t1} u
boundIn-subst {x} {t2} {y} {ƛ z t1} (inj₂ u) | ff | inj₁ v = inj₁ (inj₂ v)
boundIn-subst {x} {t2} {y} {ƛ z t1} (inj₂ u) | ff | inj₂ (v1 , v2) = inj₂ (v1 , refl , v2)

¬freeIn-subst-ok : ∀{t2 : Tm}{x : V}{t1 : Tm} →
                    ¬ freeIn x t1 →
                    [ t2 / x ]ok t1
¬freeIn-subst-ok{t2}{x}{var y} _ with y ≃ x 
¬freeIn-subst-ok{t2}{x}{var y} _ | tt = triv
¬freeIn-subst-ok{t2}{x}{var y} _ | ff = triv
¬freeIn-subst-ok{t2}{x}{t1a · t1b} nf with ¬freeIn-app{x}{t1a}{t1b} nf 
¬freeIn-subst-ok{t2}{x}{t1a · t1b} nf | nf1 , nf2 = ¬freeIn-subst-ok{t2}{x}{t1a} nf1 , ¬freeIn-subst-ok{t2}{x}{t1b} nf2
¬freeIn-subst-ok{t2}{x}{ƛ y t1} nf with ¬freeIn-lam{x}{y}{t1} nf 
¬freeIn-subst-ok{t2}{x}{ƛ y t1} nf | inj₁ p = inj₁ p
¬freeIn-subst-ok{t2}{x}{ƛ y t1} nf | inj₂ (_ , nf1) = inj₂ (inj₁ nf1)

¬freeIn-subst : ∀{x : V}{t1 t2 : Tm} →
                ¬ freeIn x t1 →
                [ t2 / x ] t1 ≡ t1
¬freeIn-subst{x}{var y}{t2} nf with keep (y ≃ x) 
¬freeIn-subst{x}{var y}{t2} nf | tt , q rewrite q | ≃-sym q with nf refl
¬freeIn-subst{x}{var y}{t2} nf | tt , q | ()
¬freeIn-subst{x}{var y}{t2} nf | ff , q rewrite q = refl
¬freeIn-subst{x}{t1a · t1b}{t2} nf with ¬freeIn-app{x}{t1a}{t1b} nf
¬freeIn-subst{x}{t1a · t1b}{t2} nf | nf1 , nf2 rewrite ¬freeIn-subst{x}{t1a}{t2} nf1 | ¬freeIn-subst{x}{t1b}{t2} nf2 = refl
¬freeIn-subst{x}{ƛ y t1}{t2} nf with ¬freeIn-lam{x}{y}{t1} nf
¬freeIn-subst{x}{ƛ y t1}{t2} nf | inj₁ e rewrite e | subst[] t1 = refl
¬freeIn-subst{x}{ƛ y t1}{t2} _ | inj₂ (e , nf) rewrite e | ¬freeIn-subst{x}{t1}{t2} nf = refl
{-
-- substituting for a variable that does not occur free does not change the term
~free-subst :
  ∀{y}{t}{t'} →
   ¬ freeIn y t →
   [ t' / y ] t ≡ t

~free-subst {y} {var x} p rewrite ~≃-symm p = refl
~free-subst {y} {t · t₁} p with ||-≡-ff{freeIn y t} p 
~free-subst {y} {t · t₁}{t'} p | p1 , p2 rewrite ~free-subst{y}{t}{t'} p1 | ~free-subst{y}{t₁}{t'} p2 = refl
~free-subst {y} {ƛ x t} p with y ≃ x
~free-subst {y} {ƛ x t} p | tt rewrite subst[] t = refl
~free-subst {y} {ƛ x t}{t'} p | ff rewrite ~free-subst{y}{t}{t'} p = refl
-}

{-
{- renaming x to y and then y back to x does not change the term, as long as
   y is not free in the term and renaming x to y would not capture y -}
rename-undo :
  ∀{x y : V}{t : Tm} →
    ¬ freeIn y t →
    renameOk x y t → 
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

-}

freeIn-subst-same : ∀{t2 : Tm}{x : V}{t1 : Tm} →
                     freeIn x ([ t2 / x ] t1) →
                     freeIn x t2
freeIn-subst-same {t2} {x} {var y} u with keep (y ≃ x)
freeIn-subst-same {t2} {x} {var y} u | tt , p rewrite p = u
freeIn-subst-same {t2} {x} {var y} u | ff , p rewrite p rewrite ≃-sym u with p
freeIn-subst-same {t2} {x} {var y} u | ff , p | ()
freeIn-subst-same {t2} {x} {t1 · t3} (inj₁ u) = freeIn-subst-same{t2}{x}{t1} u
freeIn-subst-same {t2} {x} {t1 · t3} (inj₂ u) = freeIn-subst-same{t2}{x}{t3} u
freeIn-subst-same {t2} {x} {ƛ y t1} u with x ≃ y 
freeIn-subst-same {t2} {x} {ƛ y t1} (() , _) | tt
freeIn-subst-same {t2} {x} {ƛ y t1} (_ , u) | ff = freeIn-subst-same{t2}{x}{t1} u

{-
boundIn-subst-same : ∀{t2 : Tm}{x : V}{t1 : Tm} →
                     boundIn x ([ t2 / x ] t1) →
                     boundIn x t2
boundIn-subst-same {t2} {x} {var y} u with keep (y ≃ x)
boundIn-subst-same {t2} {x} {var y} u | tt , p rewrite p = u
boundIn-subst-same {t2} {x} {var y} u | ff , p rewrite p with u
boundIn-subst-same {t2} {x} {var y} u | ff , p | ()
boundIn-subst-same {t2} {x} {t1 · t3} (inj₁ u) = boundIn-subst-same{t2}{x}{t1} u
boundIn-subst-same {t2} {x} {t1 · t3} (inj₂ u) = boundIn-subst-same{t2}{x}{t3} u
boundIn-subst-same {t2} {x} {ƛ y t1} u = {!!}
-}

bv-apart-subst1ok : ∀{t2 : Tm}{x : V}{t1 : Tm} →
                     bv-apart t2 t1 →
                     [ t2 / x ]ok t1
bv-apart-subst1ok {t2} {x} {var y} a = triv
bv-apart-subst1ok {t2} {x} {t1a · t1b} a with bv-apart-app{t2}{t1a}{t1b} a 
bv-apart-subst1ok {t2} {x} {t1a · t1b} a | a1 , a2 =
  bv-apart-subst1ok{t2}{x}{t1a} a1 , bv-apart-subst1ok{t2}{x}{t1b} a2
bv-apart-subst1ok {t2} {x} {ƛ y t1} a with bv-apart-lam{t2}{y}{t1} a
bv-apart-subst1ok {t2} {x} {ƛ y t1} a | (a1 , a2) = inj₂ (inj₂ (a1 , bv-apart-subst1ok{t2}{x}{t1} a2))

subst1ok-compose : ∀{t2 t2' : Tm}{x y : V}{t1 : Tm} →
                   [ t2 / x ]ok t1 →
                   [ t2' / x ]ok t1 →
                   [ ([ t2' / y ] t2) / x ]ok t1
subst1ok-compose {t2} {t2'} {x} {y} {var z} ok ok' with z ≃ x 
subst1ok-compose {t2} {t2'} {x} {y} {var z} ok ok' | tt = triv
subst1ok-compose {t2} {t2'} {x} {y} {var z} ok ok' | ff = triv
subst1ok-compose {t2} {t2'} {x} {y} {t1a · t1b} (oka , okb) (oka' , okb') = 
  subst1ok-compose{t2}{t2'}{x}{y}{t1a} oka oka' , subst1ok-compose{t2}{t2'}{x}{y}{t1b} okb okb'
subst1ok-compose {t2} {t2'} {x} {y} {ƛ z t1} ok ok' with x ≃ z
subst1ok-compose {t2} {t2'} {x} {y} {ƛ z t1} ok ok' | tt = inj₁ refl
subst1ok-compose {t2} {t2'} {x} {y} {ƛ z t1} (inj₁ ()) _ | ff
subst1ok-compose {t2} {t2'} {x} {y} {ƛ z t1} _ (inj₁ ()) | ff 
subst1ok-compose {t2} {t2'} {x} {y} {ƛ z t1} (inj₂ (inj₁ ok)) (inj₂ ok') | ff = inj₂ (inj₁ ok)
subst1ok-compose {t2} {t2'} {x} {y} {ƛ z t1} (inj₂ (inj₂ ok)) (inj₂ (inj₁ ok')) | ff = inj₂ (inj₁ ok')
subst1ok-compose {t2} {t2'} {x} {y} {ƛ z t1} (inj₂ (inj₂ (ok1 , ok2))) (inj₂ (inj₂ (ok1' , ok2'))) | ff =
  inj₂ (inj₂ (h , subst1ok-compose{t2}{t2'}{x}{y} ok2 ok2'))
  where h : freeIn z (subst ((y , t2') :: []) t2) → ⊥
        h f with freeIn-subst{z}{t2'}{y}{t2} f
        h f | inj₁ f1 = ok1 f1
        h f | inj₂ (f1 , f2) = ok1' f1

subst-same-commute : ∀{t : Tm}{x : V}{t1 t2 : Tm} →
                      [ t1 / x ] ([ t2 / x ] t) ≡ [ [ t1 / x ] t2 / x ] t
subst-same-commute {var y}{x} with keep (y ≃ x) 
subst-same-commute {var y}{x} | tt , p rewrite p = refl
subst-same-commute {var y}{x} | ff , p rewrite p | p = refl
subst-same-commute {ta · tb}{x}{t1}{t2} rewrite subst-same-commute{ta}{x}{t1}{t2} | subst-same-commute{tb}{x}{t1}{t2} = refl
subst-same-commute {ƛ y t}{x} with keep (x ≃ y)
subst-same-commute {ƛ y t}{x}{t1}{t2} | tt , p rewrite p | subst[] (subst [] t) = refl
subst-same-commute {ƛ y t}{x}{t1}{t2} | ff , p rewrite p | subst-same-commute{t}{x}{t1}{t2} = refl


subst-diff-commute : ∀{t : Tm}{x y : V}{t1 t2 : Tm} →
                      x ≃ y ≡ ff →
                      ¬ freeIn y t1 →
                      [ t1 / x ]ok t →
                      [ t2 / y ]ok t →                       
                      [ t1 / x ] ([ t2 / y ] t) ≡ [ [ t1 / x ] t2 / y ] ([ t1 / x ] t)
subst-diff-commute {var z}{x}{y} u _ _ _ with keep (z ≃ y) | keep (z ≃ x)
subst-diff-commute {var z}{x}{y} u _ _ _ | tt , p | tt , q rewrite p | q | ≃-≡ p | ≃-sym q with u
subst-diff-commute {var z}{x}{y} u _ _ _ | tt , p | tt , q | ()
subst-diff-commute {var z}{x}{y} u _ _ _ | tt , p | ff , q rewrite p | q with keep (z ≃ y)
subst-diff-commute {var z}{x}{y} u _ _ _ | tt , p | ff , q | tt , r rewrite p = refl
subst-diff-commute {var z}{x}{y} u _ _ _ | tt , p | ff , q | ff , r rewrite p = refl
subst-diff-commute {var z}{x}{y}{t1}{t2} u nf _ _ | ff , p | tt , q
  rewrite p | q | ¬freeIn-subst{y}{t1}{[ t1 / x ] t2} nf = refl
subst-diff-commute {var z}{x}{y} u nf _ _ | ff , p | ff , q rewrite p | q | q | p = refl
subst-diff-commute {ta · tb}{x}{y}{t1}{t2} u nf (ok1 , ok1') (ok2 , ok2')
  rewrite subst-diff-commute{ta}{x}{y}{t1}{t2} u nf ok1 ok2 | subst-diff-commute{tb}{x}{y}{t1}{t2} u nf ok1' ok2' = refl

subst-diff-commute {ƛ z t}{x}{y} u nf ok1 ok2 with keep (y ≃ z) | keep (x ≃ z)
subst-diff-commute {ƛ z t}{x}{y} u nf ok1 ok2         | tt , p | tt , q rewrite p | q = refl
subst-diff-commute {ƛ z t}{x}{y}{t1} u nf ok1 ok2     | tt , p | ff , q
  rewrite p | q | subst[] ([ t1 / x ] t) | subst[] t = refl
subst-diff-commute {ƛ z t}{x}{y}{t1}{t2} u nf ok1 ok2 | ff , p | tt , q
  rewrite p | q | subst[] ([ t2 / y ] t) | subst[] t with ok2 
subst-diff-commute {ƛ z t}{x}{y}{t1}{t2} u nf ok1 _ | ff , p | tt , q | inj₂ (inj₁ ok2)
  rewrite ¬freeIn-subst{y}{t}{t2} ok2 | ¬freeIn-subst{y}{t}{[ t1 / x ] t2} ok2 =
  refl
subst-diff-commute {ƛ z t}{x}{y}{t1}{t2} u nf ok1 _ | ff , p | tt , q | inj₂ (inj₂ (nf2 , ok2))
  rewrite ≃-≡ q | ¬freeIn-subst{z}{t2}{t1} nf2 =
  refl
subst-diff-commute {ƛ z t}{x}{y} u nf ok1 ok2 | ff , p | ff , q rewrite p | q with ok1 | ok2
subst-diff-commute {ƛ z t}{x}{y}{t1}{t2} u nf _ _ | ff , p | ff , q | inj₂ (inj₁ nf') | inj₂ ok2
  rewrite ¬freeIn-subst{x}{t}{t1} nf' with ok2
subst-diff-commute {ƛ z t}{x}{y}{t1}{t2} u nf _ _ | ff , p | ff , q | inj₂ (inj₁ nf') | inj₂ ok2 | inj₁ nf''
  rewrite ¬freeIn-subst{y}{t}{[ t1 / x ] t2} nf'' | ¬freeIn-subst{y}{t}{t2} nf''
        | ¬freeIn-subst{x}{t}{t1} nf' = refl
subst-diff-commute {ƛ z t}{x}{y}{t1}{t2} u nf _ _ | ff , p | ff , q | inj₂ (inj₁ nf') | inj₂ _ | inj₂ (nf'' , ok2)
  rewrite subst-diff-commute{t}{x}{y}{t1}{t2} u nf (¬freeIn-subst-ok{t1}{x}{t} nf') ok2 | ¬freeIn-subst{x}{t}{t1} nf' =
  refl
subst-diff-commute {ƛ z t}{x}{y}{t1}{t2} u nf _ _ | ff , p | ff , q | inj₂ (inj₂ (nf' , ok1)) | inj₂ (inj₁ nf'')
  rewrite subst-diff-commute{t}{x}{y}{t1}{t2} u nf ok1 ((¬freeIn-subst-ok{t2}{y}{t} nf'')) = 
  refl
subst-diff-commute {ƛ z t}{x}{y}{t1}{t2} u nf _ _ | ff , p | ff , q | inj₂ (inj₂ (nf' , ok1))
 | inj₂ (inj₂ (nf'' , ok2))
 rewrite subst-diff-commute{t}{x}{y}{t1}{t2} u nf ok1 ok2 =
  refl

subst1ok-subst : ∀{x y : V}{t2 t1b t1a : Tm} →
                  [ t1b / y ]ok t1a →
                  [ t2 / y ]ok t1a → 
                  [ t2 / x ]ok t1b → 
                  ¬ freeIn y t2 →
                  [ ([ t2 / x ] t1b) / y ]ok ([ t2 / x ] t1a)
subst1ok-subst {x} {y} {t2} {t1b} {var z} ok _ _ nf with keep (z ≃ x)
subst1ok-subst {x} {y} {t2} {t1b} {var z} ok _ _ nf | tt , p rewrite p = ¬freeIn-subst-ok{[ t2 / x ] t1b}{y}{t2} nf
subst1ok-subst {x} {y} {t2} {t1b} {var z} ok _ _ nf | ff , p rewrite p = triv
subst1ok-subst {x} {y} {t2} {t1b} {t1a · t1a'} (ok , ok') (okx , okx') okq nf =
  subst1ok-subst{x}{y}{t2}{t1b}{t1a} ok okx okq nf , subst1ok-subst{x}{y}{t2}{t1b}{t1a'} ok' okx' okq nf 
subst1ok-subst {x} {y} {t2} {t1b} {ƛ z t1a} ok _ _ nf with keep (y ≃ z)
subst1ok-subst {x} {y} {t2} {t1b} {ƛ z t1a} ok _ _ nf | tt , p rewrite p = inj₁ refl
subst1ok-subst {x} {y} {t2} {t1b} {ƛ z t1a} (inj₁ u) _ _ nf | ff , p rewrite p with u
subst1ok-subst {x} {y} {t2} {t1b} {ƛ z t1a} (inj₁ u) _ _ nf | ff , p | ()
subst1ok-subst {x} {y} {t2} {t1b} {ƛ z t1a} (inj₂ (inj₁ nf')) _ _ nf | ff , p rewrite p with (x ≃ z)
subst1ok-subst {x} {y} {t2} {t1b} {ƛ z t1a} (inj₂ (inj₁ nf')) _ _ nf | ff , p | tt rewrite subst[] t1a = inj₂ (inj₁ nf')
subst1ok-subst {x} {y} {t2} {t1b} {ƛ z t1a} (inj₂ (inj₁ nf')) _ _ nf | ff , p | ff = inj₂ (inj₁ h)
  where h : ¬ freeIn y ([ t2 / x ] t1a)
        h f with freeIn-subst{y}{t2}{x}{t1a} f 
        h f | inj₁ p = nf' p
        h f | inj₂ (p , q) = nf p
subst1ok-subst {x} {y} {t2} {t1b} {ƛ z t1a} (inj₂ (inj₂ (nf' , ok))) _ _ nf | ff , p rewrite p with keep (x ≃ z)
subst1ok-subst {x} {y} {t2} {t1b} {ƛ z t1a} (inj₂ (inj₂ (nf' , ok))) _ okq nf | ff , p | tt , q
  rewrite q | ≃-≡ q | ¬freeIn-subst{z}{t1b}{t2} nf' | subst[] t1a =
  inj₂ (inj₂ (nf' , ok))
subst1ok-subst {x} {y} {t2} {t1b} {ƛ z t1a} (inj₂ (inj₂ (nf' , ok))) (inj₁ okx) okq nf | ff , p | ff , q rewrite q with okx
subst1ok-subst {x} {y} {t2} {t1b} {ƛ z t1a} (inj₂ (inj₂ (nf' , ok))) (inj₁ okx) okq nf | ff , p | ff , q | ()
subst1ok-subst {x} {y} {t2} {t1b} {ƛ z t1a} (inj₂ (inj₂ (nf' , ok))) (inj₂ (inj₁ nf'')) okq nf | ff , p | ff , q rewrite q = 
  inj₂ (inj₁ h)
  where h : ¬ freeIn y ([ t2 / x ] t1a)
        h f with freeIn-subst{y}{t2}{x}{t1a} f
        h f | inj₁ f1 = nf'' f1
        h f | inj₂ (f1 , f2) = nf f1        
subst1ok-subst {x} {y} {t2} {t1b} {ƛ z t1a} (inj₂ (inj₂ (nf' , ok))) (inj₂ (inj₂ (nf'' , oku))) okq nf | ff , p | ff , q rewrite q = 
  inj₂ (inj₂ (h , subst1ok-subst{x}{y}{t2}{t1b}{t1a} ok oku okq nf ))
  where h : ¬ freeIn z ([ t2 / x ] t1b)
        h f with freeIn-subst{z}{t2}{x}{t1b} f
        h f | inj₁ f1 = nf' f1
        h f | inj₂ (f1 , f2) = nf'' f1

rename-nothing : ∀{r : Renaming}{x : V} →
                 lookup r x ≡ nothing →
                 rename-var r x ≡ x
rename-nothing {[]} {x} u = refl
rename-nothing {(y , y') :: r} {x} u with keep (x ≃ y)
rename-nothing {(y , y') :: r} {x} u | tt , p rewrite p with u
rename-nothing {(y , y') :: r} {x} u | tt , p | ()
rename-nothing {(y , y') :: r} {x} u | ff , p rewrite p | u = refl

rename-var-lem : ∀{v : V}{r : Renaming} →
                 rename r (var v) ≡ var (rename-var r v)
rename-var-lem {v} {[]} = refl
rename-var-lem {v} {(x , x') :: r} with v ≃ x
rename-var-lem {v} {(x , x') :: r} | tt = refl
rename-var-lem {v} {(x , x') :: r} | ff = rename-var-lem{v}{r}

renaming-to-subst-drop : ∀{r : Renaming}{x : V} →
                         renaming-to-subst (subst-drop x r) ≡ subst-drop x (renaming-to-subst r)
renaming-to-subst-drop {[]} {x} = refl
renaming-to-subst-drop {(y , y') :: r} {x} with y ≃ x
renaming-to-subst-drop {(y , y') :: r} {x} | tt = renaming-to-subst-drop{r}{x}
renaming-to-subst-drop {(y , y') :: r} {x} | ff rewrite renaming-to-subst-drop{r}{x} = refl

rename-subst-drop1 : ∀{x : V}{r : Renaming} →
                      rename-var (subst-drop x r) x ≡ x
rename-subst-drop1{x}{[]} = refl
rename-subst-drop1{x}{(y , y') :: r} with keep (y ≃ x) 
rename-subst-drop1{x}{(y , y') :: r} | tt , p rewrite p = rename-subst-drop1{x}{r}
rename-subst-drop1{x}{(y , y') :: r} | ff , p rewrite p | ~≃-sym p = rename-subst-drop1{x}{r}

rename-subst-drop2 : ∀{x y : V}{r : Renaming} →
                      x ≃ y ≡ ff → 
                      rename-var (subst-drop x r) y ≡ rename-var r y
rename-subst-drop2{x}{y}{[]} u = refl
rename-subst-drop2{x}{y}{(z , z') :: r} u with keep (z ≃ x) 
rename-subst-drop2{x}{y}{(z , z') :: r} u | tt , p rewrite p | rename-subst-drop2{x}{y}{r} u | ≃-≡ p | ~≃-sym u = refl
rename-subst-drop2{x}{y}{(z , z') :: r} u | ff , p rewrite p with keep (y ≃ z)
rename-subst-drop2{x}{y}{(z , z') :: r} u | ff , p | tt , q rewrite q = refl
rename-subst-drop2{x}{y}{(z , z') :: r} u | ff , p | ff , q rewrite q = rename-subst-drop2{x}{y}{r} u

rename-subst-drop : ∀{x y : V}{r : Renaming} →
                     rename-var r x ≡ x →
                     rename-var r y ≡ rename-var (subst-drop x r) y
rename-subst-drop{x}{y}{r} u with keep (x ≃ y)
rename-subst-drop{x}{y}{r} u | tt , p rewrite ≃-≡ p | rename-subst-drop1{y}{r} = u
rename-subst-drop{x}{y}{r} u | ff , p rewrite rename-subst-drop2{x}{y}{r} p = refl 

rename-subst-drop+ : ∀{x y : V}{r1 r2 : Renaming} →
                     rename-var r2 x ≡ x →
                     rename-var (r1 ++ r2) y ≡ rename-var (r1 ++ subst-drop x r2) y
rename-subst-drop+ {x} {y} {[]} {r2} u = rename-subst-drop{x}{y}{r2} u
rename-subst-drop+ {x} {y} {(z , z') :: r1} {r2} u with y ≃ z
rename-subst-drop+ {x} {y} {(z , z') :: r1} {r2} u | tt = refl
rename-subst-drop+ {x} {y} {(z , z') :: r1} {r2} u | ff = rename-subst-drop+{x}{y}{r1}{r2} u

{-
rename-var-nest : ∀{x y z : V}{r : Renaming} →
                   rename-var ((x , y) :: r) z ≡ rename-var [ x , y ] (rename-var (subst-drop x r) z)
rename-var-nest{x}{y}{z}{r} with keep (x ≃ z)
rename-var-nest{x}{y}{z}{r} | tt , p rewrite ≃-≡ p | rename-subst-drop1{z}{r} | ≃-refl{z} = refl
rename-var-nest{x}{y}{z}{r} | ff , p rewrite rename-subst-drop2{x}{z}{r} p = {!!}
-}

subst1ok-app1 : ∀{s : Subst1}{t1 t2 : Tm} →
                subst1ok s (t1 · t2) →
                subst1ok s t1
subst1ok-app1 {x , t} {t1} {t2} sok = fst sok

subst1ok-app2 : ∀{s : Subst1}{t1 t2 : Tm} →
                subst1ok s (t1 · t2) →
                subst1ok s t2
subst1ok-app2 {x , t} {t1} {t2} sok = snd sok

substOk-app1 : ∀{s : Subst}{t1 t2 : Tm} →
               substOk s (t1 · t2) →
               substOk s t1
substOk-app1 {[]} {t1} {t2} sok = triv
substOk-app1 {x :: s} {t1} {t2} (sok , sok') = subst1ok-app1 sok , substOk-app1{s}{t1}{t2} sok'

substOk-app2 : ∀{s : Subst}{t1 t2 : Tm} →
               substOk s (t1 · t2) →
               substOk s t2
substOk-app2 {[]} {t1} {t2} sok = triv
substOk-app2 {x :: s} {t1} {t2} (sok , sok') = subst1ok-app2 sok , substOk-app2{s}{t1}{t2} sok'  