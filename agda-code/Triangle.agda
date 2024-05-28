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

   This is like Takahashi's ()* operator, but it puts the resulting
   term in alpha-canonical form as it goes
-}
mpc : Tm → Renaming → Tm
mpc (var x) r = var (rename-var r x)
mpc (var x · t) r = var (rename-var r x) · mpc t r
mpc (t1 · t2 · t3) r = mpc (t1 · t2) r · mpc t3 r
mpc ((ƛ x t1) · t2) r = [ mpc t2 r / x ] mpc t1 r
mpc (ƛ x t) r =
  let x' = fresh (renaming-field r) in
    ƛ x' (mpc t ((x , x') :: r))

{-
mpc-subst1ok : ∀{t1 t2 : Tm}{x : V}{r : Renaming} →
               isSublist (renaming-dom r) (fv t2) _≃_ ≡ tt →
               isSublist (renaming-ran r) (renaming-dom r) _≃_ ≡ tt → 
                [ (mpc t2 r) / x ]ok (mpc t1 r) ≡ tt
mpc-subst1ok {var y} {t2} {x} {r} dfv rd = {!!}
mpc-subst1ok {var y · t1b} {t2} {x} {r} dfv rd = {!!}
mpc-subst1ok {(t1a · t1b) · t1c} {t2} {x} {r} dfv rd =
  &&-intro{[ (mpc t2 r) / x ]ok (mpc (t1a · t1b) r)}
    (mpc-subst1ok{t1a · t1b}{t2}{x}{r} dfv rd)
    (mpc-subst1ok{t1c}{t2}{x}{r} dfv rd)
mpc-subst1ok {ƛ y t1a · t1b} {t2} {x} {r} dfv rd = {!!}
mpc-subst1ok {ƛ y t1} {t2} {x} {r} dfv rd = {!!}

-}

mpc-completion : ∀{t1 t2 : Tm}{r : Renaming} →
                  list-all (λ x → rename-var r x ≃ x) (fv t1) ≡ tt →
                  isSublist (renaming-ran r) (renaming-dom r) _≃_ ≡ tt → 
                  t1 ⟨ ⇒ ⟩ t2 →
                  t2 ⟨ ⇒ ⟩ mpc t1 r
mpc-completion{r = r} dfv rd (⇒var{v}) with rename-var r v 
mpc-completion{r = r} dfv rd (⇒var{v})| q with &&-elim {q ≃ v} dfv
mpc-completion{r = r} dfv rd (⇒var{v})| q | p , _ rewrite ≃-≡ p = ⇒var
mpc-completion dfv rd (⇒app{t1a}{t1a'}{t1b}{t1b'}{c} d1 d2 (inj₁ refl)) = {!!}
mpc-completion dfv rd (⇒app{t1a}{t1a'}{t1b}{t1b'}{c} d1 d2 (inj₂ b)) = {!!}
mpc-completion{t1 = ƛ x t1}{r = r} dfv rd (⇒lam d (inj₁ refl)) =
  let z = fresh (renaming-field r) in
   ⇒lam{t1' = mpc t1 r} (mpc-completion {!!} {!!} d) (inj₂ ( {!!} , {!!} , {!!} , {!!}))
mpc-completion{t1 = ƛ x t1}{t2 = ƛ y t2}{r = r} dfv rd (⇒lam d (inj₂ (ro , fi , diff , refl))) = {!!}
{-
  let z = fresh (renaming-field r) in
    ⇒lam{y}{t1' = (mpc t1 ((x , z) :: r))} {!!} {!!}
-}