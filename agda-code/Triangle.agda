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
open import FreeVars vi 
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

mpcOk : Tm → 𝔹
mpcOk (var x) = tt
mpcOk (var x · t) = mpcOk t
mpcOk (t1 · t2 · t3) = mpcOk (t1 · t2) && mpcOk t3
mpcOk ((ƛ x t1) · t2) = [ t2 / x ]ok t1 && mpcOk t1 && mpcOk t2
mpcOk (ƛ x t) = mpcOk t

mpc-completion : ∀{t1 t2 : Tm} → 
                  mpcOk t1 ≡ tt → 
                  t1 ⟨ ⇒ ⟩ t2 →
                  t2 ⟨ ⇒ ⟩ mpc t1
mpc-completion ok ⇒var = ⇒var 
mpc-completion ok (⇒app ⇒var d2 (inj₁ refl)) = ⇒app ⇒var (mpc-completion ok d2) (inj₁ refl)
mpc-completion ok (⇒app{t1 = t1a · t1b}{t2 = t2}{t2'} d1 d2 (inj₁ refl)) with &&-elim {mpcOk (t1a · t1b)} ok
mpc-completion ok (⇒app{t1 = t1a · t1b}{t2 = t2}{t2'} d1 d2 (inj₁ refl)) | ok1 , ok2 =
  ⇒app (mpc-completion ok1 d1) (mpc-completion ok2 d2) (inj₁ refl)
mpc-completion ok (⇒app{t2 = t2}{t2'} (⇒lam{x = x}{t1 = t1}{t1' = t1'} d) d2 (inj₁ refl))
  with &&-elim{[ t2 / x ]ok t1} ok
mpc-completion _ (⇒app{t2 = t2}{t2'} (⇒lam{x = x}{t1 = t1}{t1' = t1'} d) d2 (inj₁ refl)) | sok , p
  with &&-elim{mpcOk t1} p
mpc-completion _ (⇒app{t2 = t2}{t2'} (⇒lam{x = x}{t1 = t1}{t1' = t1'} d1) d2 (inj₁ refl))
  | sok , _ | ok1 , ok2 = ⇒app (⇒lam (mpc-completion ok1 d1)) (mpc-completion ok2 d2) (inj₂ ( {!!} , refl))

mpc-completion ok (⇒app{t1 = t1}{ƛ x t1'}{t2}{t2'} d1 d2 (inj₂ (b1 , b2))) = {!!}
mpc-completion ok (⇒lam d) = ⇒lam (mpc-completion ok d)

{-
-}