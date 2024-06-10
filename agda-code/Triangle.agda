{- -}
open import lib
open import relations
open import VarInterface

module Triangle(vi : VI) where

open VI vi
open import Tm vi
open import Subst vi
open import Beta vi
open import Alpha vi 
open import Parallel vi 

{- maximal parallel contraction

   This is Takahashi's ()* operator
-}
mpc : Tm → Tm
mpc (var x) = var x
mpc (var x · t) = var x · mpc t 
mpc (t1 · t2 · t3) = mpc (t1 · t2) · mpc t3
mpc ((ƛ x t1) · t2) = [ mpc t2 / x ] mpc t1
mpc (ƛ x t) = ƛ x (mpc t)

mpcOk : Tm → Set
mpcOk (var x) = ⊤
mpcOk (var x · t) = mpcOk t
mpcOk (t1 · t2 · t3) = mpcOk (t1 · t2) ∧ mpcOk t3
mpcOk ((ƛ x t1) · t2) = bv-apart t2 t1 ∧ mpcOk t1 ∧ mpcOk t2
mpcOk (ƛ x t) = mpcOk t

freeIn-mpc : ∀{x : V}{t : Tm} → freeIn x (mpc t) → freeIn x t
freeIn-mpc {x} {var y} u = u
freeIn-mpc {x} {var y · t2} (inj₁ p) = inj₁ p
freeIn-mpc {x} {var y · t2} (inj₂ p) = inj₂ (freeIn-mpc{x}{t2} p)
freeIn-mpc {x} {t1 · t2 · t3} (inj₁ p) = inj₁ (freeIn-mpc{x}{t1 · t2} p)
freeIn-mpc {x} {t1 · t2 · t3} (inj₂ p) = inj₂ (freeIn-mpc{x}{t3} p)
freeIn-mpc {x} {(ƛ y t1) · t2} u with keep (x ≃ y)
freeIn-mpc {x} {(ƛ y t1) · t2} u | tt , eq rewrite ≃-≡ eq =
  inj₂ (freeIn-mpc{y}{t2} (freeIn-subst-same{mpc t2}{y}{mpc t1} u))
freeIn-mpc {x} {(ƛ y t1) · t2} u | ff , eq with freeIn-subst{x}{mpc t2}{y}{mpc t1} u
freeIn-mpc {x} {(ƛ y t1) · t2} u | ff , eq | inj₁ p = inj₁ (eq , freeIn-mpc{x}{t1} p)
freeIn-mpc {x} {(ƛ y t1) · t2} u | ff , eq | inj₂ (p1 , p2) = inj₂ (freeIn-mpc{x}{t2} p1)
freeIn-mpc {x} {ƛ y t} (u1 , u2) = u1 , freeIn-mpc{x}{t} u2

boundIn-mpc : ∀{x : V}{t : Tm} → boundIn x (mpc t) → boundIn x t
boundIn-mpc {x} {var y} u = u
boundIn-mpc {x} {var y · t2} (inj₁ ())
boundIn-mpc {x} {var y · t2} (inj₂ p) = inj₂ (boundIn-mpc{x}{t2} p)
boundIn-mpc {x} {t1 · t2 · t3} (inj₁ p) = inj₁ (boundIn-mpc{x}{t1 · t2} p)
boundIn-mpc {x} {t1 · t2 · t3} (inj₂ p) = inj₂ (boundIn-mpc{x}{t3} p)
boundIn-mpc {x} {(ƛ y t1) · t2} u with boundIn-subst{x}{mpc t2}{y}{mpc t1} u
boundIn-mpc {x} {(ƛ y t1) · t2} u | inj₁ v = inj₁ (inj₂ (boundIn-mpc{x}{t1} v))
boundIn-mpc {x} {(ƛ y t1) · t2} u | inj₂ (v1 , v2) = inj₂ (boundIn-mpc{x}{t2} v1)
boundIn-mpc {x} {ƛ y t} (inj₁ u) = inj₁ u
boundIn-mpc {x} {ƛ y t} (inj₂ u) = inj₂ (boundIn-mpc{x}{t} u)

bv-apart-mpc : ∀{t2 t1 : Tm} → 
                 bv-apart t2 t1 →
                 bv-apart (mpc t2) (mpc t1)
bv-apart-mpc{t2}{t1} u x q1 q2 with u x (freeIn-mpc{x}{t2} q1)
bv-apart-mpc{t2}{t1} u x q1 q2 | r = r (boundIn-mpc{x}{t1} q2)

mpc-completion : ∀{t1 t2 : Tm} → 
                  mpcOk t1 → 
                  t1 ⟨ ⇒ ⟩ t2 →
                  t2 ⟨ ⇒ ⟩ mpc t1
mpc-completion ok ⇒var = ⇒var
mpc-completion{(var x) · t1}{t2} ok (⇒app{t2' = t2'} ⇒var d2) = ⇒app ⇒var (mpc-completion{t1}{t2'} ok d2)
mpc-completion{t1a · t1b · t1c}{t2} (ok1 , ok2) (⇒app{t1' = t1'}{t2' = t2'} d1 d2) =
  ⇒app (mpc-completion{t1a · t1b}{t1'} ok1 d1) (mpc-completion{t1c}{t2'} ok2 d2)
mpc-completion{(ƛ x t1a) · t1b}{t2} (a , ok1 , ok2) (⇒app{t2' = t2'} (⇒lam{t1 = t1a}{t1'} d1) d2) = 
  ⇒beta (mpc-completion{t1a}{t1'} ok1 d1) ((mpc-completion{t1b}{t2'} ok2 d2)) ((bv-apart-subst1ok (bv-apart-mpc a) , triv) , refl)
mpc-completion ok (⇒lam d) = ⇒lam (mpc-completion ok d)
mpc-completion (a , ok1 , ok2) (⇒beta{x}{t1}{t1'}{t2}{t2'} d1 d2 ((s , _) , refl)) =
  ⇒-subst{x}{t1'}{mpc t1}{t2'}{mpc t2}
    (mpc-completion ok1 d1) (mpc-completion ok2 d2)
    λ x f nb → a x (⇒-freeIn f d2) (⇒-boundIn nb d1)
