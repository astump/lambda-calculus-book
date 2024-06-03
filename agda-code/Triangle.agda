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
mpcOk ((ƛ x t1) · t2) = bv-apart t2 t1 && mpcOk t1 && mpcOk t2
mpcOk (ƛ x t) = mpcOk t

bv-subst : ∀{t2 : Tm}{x : V}{t1 : Tm} →
            isSublist (bv ([ t2 / x ] t1)) (bv t2 ++ bv t1) _≃_ ≡ tt
bv-subst {t2} {x} {var y} with y ≃ x
bv-subst {t2} {x} {var y} | tt rewrite ++[] (bv t2) = isSublist-refl{V}{_≃_} ≃-refl {bv t2}
bv-subst {t2} {x} {var y} | ff = refl
bv-subst {t2} {x} {t1a · t1b} with bv-subst{t2}{x}{t1a} | bv-subst{t2}{x}{t1b} 
bv-subst {t2} {x} {t1a · t1b} | r1 | r2
  rewrite list-all-append (λ a → list-member _≃_ a (bv t2 ++ bv t1a ++ bv t1b))
                          (bv (subst ((x , t2) :: []) t1a)) (bv (subst ((x , t2) :: []) t1b)) =
  &&-intro{list-all
      (λ a → list-member _≃_ a (bv t2 ++ bv t1a ++ bv t1b))
      (bv (subst ((x , t2) :: []) t1a))}
      (list-all-sub (bv (subst ((x , t2) :: []) t1a))
        (λ a u → list-member-sub{V}{eq = _≃_}{a}{bv t2 ++ bv t1a}{bv t2 ++ bv t1a ++ bv t1b} ≃-≡ u
                  h1) r1)
      (list-all-sub (bv (subst ((x , t2) :: []) t1b))
        (λ a u → list-member-sub{V}{eq = _≃_}{a}{bv t2 ++ bv t1b}{bv t2 ++ bv t1a ++ bv t1b} ≃-≡ u
                  h2) r2)
  where h1 : isSublist (bv t2 ++ bv t1a) (bv t2 ++ bv t1a ++ bv t1b) _≃_ ≡ tt
        h1 rewrite sym (++-assoc (bv t2) (bv t1a) (bv t1b)) =
          isSublist-++1{eq = _≃_}{l1 = bv t2 ++ bv t1a} ≃-refl
        h2 : isSublist (bv t2 ++ bv t1b) (bv t2 ++ bv t1a ++ bv t1b) _≃_ ≡ tt
        h2 = isSublist-++-cong{eq = _≃_}{bv t2}{bv t1b}{bv t1a ++ bv t1b} ≃-refl
               (isSublist-++2{eq = _≃_}{bv t1a}{bv t1b}{bv t1b} ≃-refl (isSublist-refl ≃-refl {bv t1b}))

bv-subst {t2} {x} {ƛ y t1} rewrite sym (++-singleton y (bv t2) (bv t1)) with x ≃ y | list-member-++2 _≃_ y (bv t2 ++ [ y ]) (bv t1) (list-member-++3 _≃_ y (bv t2) [ y ] (||-intro1 (≃-refl {y})))
bv-subst {t2} {x} {ƛ y t1} | tt | p rewrite subst[] t1 rewrite
  isSublist-++2{eq = _≃_}{bv t2 ++ [ y ]}{bv t1}{bv t1} ≃-refl (isSublist-refl ≃-refl {bv t1})
  | &&-tt (list-member _≃_ y ((bv t2 ++ [ y ]) ++ bv t1)) = p
  
bv-subst {t2} {x} {ƛ y t1} | ff | p rewrite p | ++-singleton y (bv t2) (bv t1) =
  list-all-sub{p = λ a → list-member _≃_ a (bv t2 ++ bv t1)} (bv (subst ((x , t2) :: []) t1)) 
    (λ a u → list-member-sub{eq = _≃_}{a}{(bv t2 ++ bv t1)}{bv t2 ++ y :: bv t1} ≃-≡
                u (isSublist-++-cong {eq = _≃_} {bv t2} {bv t1} {y :: bv t1} ≃-refl
                     (isSublist-++2{eq = _≃_}{[ y ]}{bv t1}{bv t1} ≃-refl (isSublist-refl ≃-refl {bv t1})))) 
    (bv-subst{t2}{x}{t1})

bv-isSublist-mpc : ∀{t : Tm} →
                    isSublist (bv (mpc t)) (bv t) _≃_ ≡ tt
bv-isSublist-mpc {var x} = refl
bv-isSublist-mpc {var x · t} = bv-isSublist-mpc{t}
bv-isSublist-mpc {t1 · t2 · t3} =
  isSublist-++-merge{eq = _≃_}{bv (mpc (t1 · t2))}{bv (t1 · t2)}{bv (mpc t3)}{bv t3} ≃-≡ ≃-refl
    (bv-isSublist-mpc{t1 · t2}) (bv-isSublist-mpc{t3})
bv-isSublist-mpc {(ƛ x t1) · t2} =
  isSublist-trans {eq = _≃_} {bv ([ mpc t2 / x ] mpc t1)}
    {bv (mpc t2) ++ bv (mpc t1)} {x :: bv t1 ++ bv t2} ≃-≡ (bv-subst{mpc t2}{x}{mpc t1})
    ((isSublist-trans{eq = _≃_}{bv (mpc t2) ++ bv (mpc t1)}{bv t2 ++ bv t1}{x :: bv t1 ++ bv t2}
      ≃-≡ (isSublist-++-merge {eq = _≃_} {bv (mpc t2)} {bv t2} {bv (mpc t1)}
             {bv t1} ≃-≡ ≃-refl (bv-isSublist-mpc{t2}) (bv-isSublist-mpc{t1})))
             {!isSublist-++2{eq = _≃_}{[ x ]}{bv t1 ++ bv t2}{bv t1 ++ bv t2} ≃-refl (isSublist-refl ≃-refl {bv t1 ++ bv t2})!})
bv-isSublist-mpc {ƛ x t} = {!!}

fv-isSublist-mpc : ∀{t : Tm} →
                    isSublist  (fv (mpc t)) (fv t) _≃_ ≡ tt
fv-isSublist-mpc {t} = {!!}

bv-apart-mpc : ∀ (t2 t1 : Tm) →
                 bv-apart t2 t1 ≡ tt →
                 bv-apart (mpc t2) (mpc t1) ≡ tt
bv-apart-mpc = {!!}

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
  with &&-elim{bv-apart t2 t1} ok
mpc-completion _ (⇒app{t2 = t2}{t2'} (⇒lam{x = x}{t1 = t1}{t1' = t1'} d) d2 (inj₁ refl)) | sok , p
  with &&-elim{mpcOk t1} p
mpc-completion _ (⇒app{t2 = t2}{t2'} (⇒lam{x = x}{t1 = t1}{t1' = t1'} d1) d2 (inj₁ refl))
  | sok , _ | ok1 , ok2 = ⇒app (⇒lam (mpc-completion ok1 d1)) (mpc-completion ok2 d2) (inj₂ ( {!!} , refl))

mpc-completion ok (⇒app{t1 = t1}{ƛ x t1'}{t2}{t2'} d1 d2 (inj₂ (b1 , b2))) = {!!}
mpc-completion ok (⇒lam d) = ⇒lam (mpc-completion ok d)

{-
-}