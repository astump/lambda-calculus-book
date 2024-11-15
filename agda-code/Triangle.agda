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

----------------------------------------------------------------------

αcanonh : Tm → 𝕃 V → Renaming → Tm
αcanonh (var x) avoid r = var (rename-var r x)
αcanonh (t1 · t2) avoid r = αcanonh t1 avoid r · αcanonh t2 avoid r 
αcanonh (ƛ x t) avoid r =
  let x' = fresh avoid in
    ƛ x' (αcanonh t (x' :: avoid) ((x , x') :: r))

αcanon : Tm → Tm
αcanon t = αcanonh t (vars t) []

boundIn-αcanon : ∀{avoid : 𝕃 V}{r : Renaming}{t : Tm}{x : V} → 
                  boundIn x (αcanonh t avoid r) →
                  list-member _≃_ x avoid ≡ ff
boundIn-αcanon{avoid}{r}{var x}{y} ()
boundIn-αcanon{avoid}{r}{t1 · t2}{y} (inj₁ b) = boundIn-αcanon{avoid}{r}{t1}{y} b
boundIn-αcanon{avoid}{r}{t1 · t2}{y} (inj₂ b) = boundIn-αcanon{avoid}{r}{t2}{y} b
boundIn-αcanon{avoid}{r}{ƛ x t1}{y} (inj₁ b) rewrite ≃-≡ b = fresh-distinct{avoid}
boundIn-αcanon{avoid}{r}{ƛ x t1}{y} (inj₂ b) =
  snd (||-≡-ff{y ≃ fresh avoid} (boundIn-αcanon{fresh avoid :: avoid}{(x , fresh avoid) :: r}{t1}{y} b))

boundIn-αcanon' : ∀{avoid : 𝕃 V}{r : Renaming}{t : Tm}{x : V} → 
                   list-member _≃_ x avoid ≡ tt →
                   ¬ boundIn x (αcanonh t avoid r)
boundIn-αcanon'{avoid}{r}{t}{x} m b with boundIn-αcanon{avoid}{r}{t}{x} b
boundIn-αcanon'{avoid}{r}{t}{x} m b | q rewrite q with m
boundIn-αcanon'{avoid}{r}{t}{x} m b | q | ()

freeIn-αcanon : ∀{avoid : 𝕃 V}{r : Renaming}{t : Tm}{x : V} →
                  (∀ {x} → freeIn x t → list-member _≃_ (rename-var r x) avoid ≡ tt) →
                  isSublist (renaming-ran r) avoid _≃_ ≡ tt →
                  freeIn x (αcanonh t avoid r) →
                  list-member _≃_ x avoid ≡ tt
freeIn-αcanon{avoid}{[]}{var y}{x} fa sr fi = fa fi
freeIn-αcanon{avoid}{(z , z') :: r}{var y}{x} fa sr fi with keep (y ≃ z)
freeIn-αcanon{avoid}{(z , z') :: r}{var y}{x} fa sr fi | tt , p rewrite p | ≃-≡ fi = &&-elim1{list-member _≃_ z' avoid} sr
freeIn-αcanon{avoid}{(z , z') :: r}{var y}{x} fa sr fi | ff , p rewrite p =
  freeIn-αcanon{avoid}{r}{var y}{x} h (&&-elim2{list-member _≃_ z' avoid} sr) fi
  where h : ∀{x' : V} → x' ≃ y ≡ tt → list-member _≃_ (rename-var r x') avoid ≡ tt
        h{x'} eq rewrite sym (≃-≡ eq) with fa{x'} (≃-refl{x'})
        h{x'} eq | q rewrite p = q
freeIn-αcanon{avoid}{r}{t1 · t2}{x} fa sr (inj₁ fi) = freeIn-αcanon{avoid}{r}{t1}{x} (λ {q} f → fa {q} (inj₁ f)) sr fi
freeIn-αcanon{avoid}{r}{t1 · t2}{x} fa sr (inj₂ fi) = freeIn-αcanon{avoid}{r}{t2}{x} (λ {q} f → fa {q} (inj₂ f)) sr fi
freeIn-αcanon{avoid}{r}{ƛ y t}{x} fa sr (fi , fi') with
  freeIn-αcanon{fresh avoid :: avoid}{(y , fresh avoid) :: r}{t}{x} h
    (isSublist-++-cong {V} {_≃_} {[ fresh avoid ]} {renaming-ran r}
                       {avoid} ≃-refl sr) fi'
  where
   h : {z : V} →
       freeIn z t →
       (rename-var ((y , fresh avoid) :: r) z ≃ fresh avoid) ||
       list-member _≃_ (rename-var ((y , fresh avoid) :: r) z) avoid ≡ tt
   h {z} fz with keep (z ≃ y)
   h {z} fz | tt , p rewrite p = ||-intro1 ≃-refl
   h {z} fz | ff , p rewrite p = ||-intro2 (fa {z} (p , fz))
freeIn-αcanon{avoid}{r}{ƛ y t}{x} fa sr (fi , fi') | p rewrite fi = p



mpcOk-αcanon : ∀{avoid : 𝕃 V}{r : Renaming}{t : Tm} → 
                  (∀ {x} → freeIn x t → list-member _≃_ (rename-var r x) avoid ≡ tt) →
                  isSublist (renaming-ran r) avoid _≃_ ≡ tt →
                  mpcOk (αcanonh t avoid r)
mpcOk-αcanon{avoid}{r}{var x} fa sr = triv
mpcOk-αcanon{avoid}{r}{(var x) · t} fa sr = mpcOk-αcanon{avoid}{r}{t} (λ {y} f → fa {y} (inj₂ f)) sr
mpcOk-αcanon{avoid}{r}{t1 · t2 · t3} fa sr =
  mpcOk-αcanon{avoid}{r}{t1 · t2} (λ {y} f → fa {y} (inj₁ f)) sr ,
  mpcOk-αcanon{avoid}{r}{t3} ((λ {y} f → fa {y} (inj₂ f))) sr   
mpcOk-αcanon{avoid}{r}{(ƛ y t1) · t2} fa sr =
  h' ,
  mpcOk-αcanon{fresh avoid :: avoid}{(y , fresh avoid) :: r}{t1} h
    (isSublist-++-cong {V} {_≃_} {[ fresh avoid ]} {renaming-ran r}
                       {avoid} ≃-refl sr) ,
  mpcOk-αcanon{avoid}{r}{t2} (λ {z} f → fa {z} (inj₂ f)) sr
  where
   h : {z : V} →
       freeIn z t1 →
       (rename-var ((y , fresh avoid) :: r) z ≃ fresh avoid) ||
       list-member _≃_ (rename-var ((y , fresh avoid) :: r) z) avoid ≡ tt
   h {z} fz with keep (z ≃ y)
   h {z} fz | tt , p rewrite p = ||-intro1 ≃-refl
   h {z} fz | ff , p rewrite p = ||-intro2 (fa {z} (inj₁ (p , fz)))

   h' : bv-apart (αcanonh t2 avoid r)
         (αcanonh t1 (fresh avoid :: avoid) ((y , fresh avoid) :: r))
   h' x f = boundIn-αcanon'{fresh avoid :: avoid}{(y , fresh avoid) :: r}{t1}{x}
              (||-intro2{x ≃ fresh avoid} (freeIn-αcanon{avoid}{r}{t2}{x} (λ {z} f → fa {z} (inj₂ f)) sr f))

mpcOk-αcanon{avoid}{r}{ƛ y t} fa sr =
  mpcOk-αcanon{fresh avoid :: avoid}{(y , fresh avoid) :: r}{t} h
    (isSublist-++-cong {V} {_≃_} {[ fresh avoid ]} {renaming-ran r}
                       {avoid} ≃-refl sr)
  where
   h : {z : V} →
       freeIn z t →
       (rename-var ((y , fresh avoid) :: r) z ≃ fresh avoid) ||
       list-member _≃_ (rename-var ((y , fresh avoid) :: r) z) avoid ≡ tt
   h {z} fz with keep (z ≃ y)
   h {z} fz | tt , p rewrite p = ||-intro1 ≃-refl
   h {z} fz | ff , p rewrite p = ||-intro2 (fa {z} (p , fz))


αcanon-triv-renaming : ∀{x : V}{r1 r2 : Renaming}{avoid : 𝕃 V}{t : Tm} →
                         rename-var r2 x ≡ x → 
                         αcanonh t avoid (r1 ++ r2) ≡ αcanonh t avoid (r1 ++ subst-drop x r2)
αcanon-triv-renaming{x}{r1}{r2}{avoid}{var y} u rewrite rename-subst-drop+{x}{y}{r1}{r2} u = refl
αcanon-triv-renaming{x}{r1}{r2}{avoid}{t1 · t2} u
  rewrite αcanon-triv-renaming{x}{r1}{r2}{avoid}{t1} u | αcanon-triv-renaming{x}{r1}{r2}{avoid}{t2} u = refl
αcanon-triv-renaming{x}{r1}{r2}{avoid}{ƛ y t} u
  rewrite αcanon-triv-renaming{x}{(y , fresh avoid) :: r1}{r2}{fresh avoid :: avoid}{t} u = refl

αcanon-¬freeIn : ∀{x : V}{r : Renaming}{avoid : 𝕃 V}{t : Tm} → 
                  (rename-var r x ≃ x) ≡ ff →
                  list-member _≃_ x (renaming-ran r) ≡ ff →
                  ¬ freeIn x (αcanonh t avoid r)
αcanon-¬freeIn = {!!}

subst-free-αcanon : ∀{z z' : V}{t : Tm}{avoid : 𝕃 V}{r r' : Renaming} →
                     z ≃ z' ≡ ff → 
                     rename-var r' z ≡ z' → 
                     < z ↦ z' > (αcanonh t avoid (subst-drop z r)) ≡
                     αcanonh t avoid (r' ++ (subst-drop z r))
subst-free-αcanon {z} {z'} {var x} {avoid} {r} {r'} u rv with keep (x ≃ z) 
subst-free-αcanon {z} {z'} {var x} {avoid} {r} {r'} u rv | tt , p
  rewrite ≃-≡ p | rename-subst-drop1{z}{r} | ≃-refl{z} | rename-var-++{z}{z'}{r'}{subst-drop z r} u rv = refl
subst-free-αcanon {z} {z'} {var x} {avoid} {r} {r'} u rv | ff , p
  rewrite rename-subst-drop2{z}{x}{r} (~≃-sym p) = {!!} 
{-
Goal: (< z ↦ z' > var (rename-var r x)) ≡
      var (rename-var (r' ++ subst-drop z r) x)

from

 Goal: (< z ↦ z' > var (rename-var (subst-drop z r) x)) ≡
      var (rename-var (r' ++ subst-drop z r) x)
-}
subst-free-αcanon {z} {z'} {t1 · t2} {avoid} {r} {r'} u rv = {!!}
subst-free-αcanon {z} {z'} {ƛ x t} {avoid} {r} {r'} u rv = {!!}

rename-var-avoid : ∀{x : V}{r : Renaming}{avoid : 𝕃 V} → 
                    (rename-var r x ≃ x) ≡ ff → 
                    isSublist (renaming-dom r) avoid _≃_ ≡ tt → 
                    x ≃ fresh avoid ≡ ff 
rename-var-avoid {x} {[]} {avoid} u da rewrite ≃-refl{x} with u
rename-var-avoid {x} {[]} {avoid} u da | ()
rename-var-avoid {x} {(x' , y) :: r} {avoid} u da with keep (x ≃ x')
rename-var-avoid {x} {(x' , y) :: r} {avoid} u da | tt , p rewrite p | sym (≃-≡ p) with fresh-distinct{avoid} | keep (x ≃ fresh avoid)
rename-var-avoid {x} {(x' , y) :: r} {avoid} u da | tt , p | dis | tt , q rewrite ≃-≡ q with &&-elim1{list-member _≃_ (fresh avoid) avoid} da 
rename-var-avoid {x} {(x' , y) :: r} {avoid} u da | tt , p | dis | tt , q | mem rewrite mem with dis
rename-var-avoid {x} {(x' , y) :: r} {avoid} u da | tt , p | dis | tt , q | mem | ()
rename-var-avoid {x} {(x' , y) :: r} {avoid} u da | tt , p | dis | ff , q = q
rename-var-avoid {x} {(x' , y) :: r} {avoid} u da | ff , p rewrite p =
  rename-var-avoid {x} {r} {avoid} u (&&-elim2{list-member _≃_ x' avoid} da)

αcanon-rename-var : ∀{z x : V}{r : Renaming} → 
                    disjoint _≃_ (renaming-ran r) (renaming-dom r) ≡ tt →
                    z ≃ x ≡ ff →
                    list-member _≃_ x (renaming-dom r) ≡ tt → 
                    rename-var r z ≃ x ≡ ff 
αcanon-rename-var {z} {x} {r} dis u memx with keep (rename-var r z ≃ z)
αcanon-rename-var {z} {x} {r} dis u memx | tt , p rewrite ≃-≡ p = u
αcanon-rename-var {z} {x} {r} dis u memx | ff , p = 
  disjoint-in-out{l1 = renaming-ran r}{l2 = renaming-dom r} ≃-≡ dis (rename-var-member-ran{z}{r} p) memx

αcanon-rename : ∀{t : Tm}{x : V}{r : Renaming}{avoid : 𝕃 V} → 
                 disjoint _≃_ (renaming-ran r) (renaming-dom r) ≡ tt →
                 isSublist (renaming-dom r) avoid _≃_ ≡ tt → 
                 disjoint _≃_ (renaming-ran r) (vars t) ≡ tt → 
                 isSublist (vars t) avoid _≃_ ≡ tt → 
                 rename-var r x ≃ x ≡ ff → 
                 αcanonh t avoid r
              ≡ < x ↦ rename-var r x > αcanonh t avoid (subst-drop x r)

αcanon-rename {var z} {x} {r} dis _ _ _ xmapped with keep (z ≃ x)
αcanon-rename {var z} {x} {r} dis _ _ _ _ | tt , p rewrite ≃-≡ p | rename-subst-drop1{x}{r} | ≃-refl{x} = refl
αcanon-rename {var z} {x} {r} dis _ _ _ xmapped | ff , p
  rewrite rename-subst-drop2{x}{z}{r} (~≃-sym p) | αcanon-rename-var{z}{x}{r} dis p (rename-var-member-dom{x}{r} xmapped) = refl

αcanon-rename{t1 · t2}{x}{r}{avoid} dis dsub rv vsub xmapped
 rewrite αcanon-rename{t1}{x}{r}{avoid} dis dsub
           (fst (disjoint-++{l1 = renaming-ran r}{vars t1} rv))
           (isSublist-++1l{V}{_≃_}{vars t1}{vars t2}{avoid} vsub) xmapped
       | αcanon-rename{t2}{x}{r}{avoid} dis dsub
           (snd (disjoint-++{l1 = renaming-ran r}{vars t1} rv))
           (isSublist-++2l{V}{_≃_}{vars t1}{vars t2}{avoid} vsub) xmapped
     = refl

αcanon-rename{ƛ z t}{x}{r}{avoid} dis dsub rv vsub xmapped = q
  where h : x ≃ fresh avoid ≡ ff
        h = member-in-out{V}{avoid}{x}{fresh avoid}{_≃_} ≃-≡
             (list-member-sub{V}{_≃_}{x}{renaming-dom r}{avoid} ≃-≡ (rename-var-member-dom {x} {r} xmapped) dsub) (fresh-distinct{avoid})
             
        dx : rename-var ((z , fresh avoid) :: r) x ≃ x ≡ ff
        dx with x ≃ z
        dx | tt = ~≃-sym h
        dx | ff = xmapped        

        goal : Set 
        goal = ƛ (fresh avoid)
           (αcanonh t (fresh avoid :: avoid) ((z , fresh avoid) :: r))
           ≡
           (< x ↦ rename-var r x >
            ƛ (fresh avoid)
              (αcanonh t (fresh avoid :: avoid)
                ((z , fresh avoid) :: subst-drop x r)))

        q : goal
        q with (&&-elim{list-member _≃_ z avoid} vsub) 
        q | vsub1 , vsub2 = q2
          where
           r1 : fresh avoid ≃ z ≡ ff
           r1 = ~≃-sym (member-in-out{l = avoid} ≃-≡ vsub1 (fresh-distinct{avoid}))

           q5 : rename-var ((z , fresh avoid) :: subst-drop z r) z ≃ z ≡ ff
           q5 rewrite ≃-refl{z} = r1

           q6 : (z ≃ fresh avoid) ||
                list-member _≃_ z (map snd (subst-drop z r))
                ≡ ff
           q6 rewrite ~≃-sym r1 =
             list-member-sub-ff{l1 = renaming-ran (subst-drop z r)}{renaming-ran r}
               ≃-≡ (subst-drop-sublist{s = r})
               (list-member-list-all-ff{eq = _≃_}{z}{renaming-ran r}
                 (list-all-sub (renaming-ran r) (λ a u → ~≃-sym2 (~||-elim1 u)) rv))

           q2 : goal
           q2 rewrite h | αcanon-rename{t}{x}{(z , fresh avoid) :: r}{fresh avoid :: avoid}
                            (&&-intro{~ (list-member _≃_ (fresh avoid) (z :: renaming-dom r))}
                              (~||-intro r1
                                (list-member-sub-ff{l1 = renaming-dom r}{avoid}
                                  ≃-≡ dsub (fresh-distinct{l = avoid})))
                              (list-all-sub{p = λ a → ~ (a ≃ z) && ~ (list-member _≃_ a (renaming-dom r))}
                                (renaming-ran r)
                                (λ a p → ~||-intro{a ≃ z} (~-≡-tt (&&-elim1 p)) (~-≡-tt (&&-elim2 p)))
                                (list-all-&&{p = λ a → ~ (a ≃ z)} (renaming-ran r)
                                   (list-all-sub {p = λ a → ~ ((a ≃ z) || list-member _≃_ a (vars t))}
                                       (renaming-ran r) (λ a p → ~||-elim1{a ≃ z} p) rv) dis)))
                            (&&-intro {list-member _≃_ z (fresh avoid :: avoid)}
                             (||-intro2{z ≃ fresh avoid} vsub1)
                              (list-all-sub (renaming-dom r) (λ a m → ||-intro2{a ≃ fresh avoid} m) dsub))
                            (&&-intro {~ list-member _≃_ (fresh avoid) (vars t)}
                              (~-≡-ff (list-member-sub-ff{a = fresh avoid}{vars t}{avoid} ≃-≡
                                vsub2 (fresh-distinct{avoid})))
                              (list-all-sub (renaming-ran r) (λ a p → ~||-elim2 p) rv)) 
                            (isSublist-++2 {V} {_≃_} {[ fresh avoid ]} {vars t} {avoid}
                              ≃-refl vsub2)
                            dx
                         with keep (x ≃ z)
           q2 | ff , p rewrite p | ~≃-sym p = refl
           q2 | tt , p rewrite ≃-≡ p | ≃-refl{z} 
                             | ¬freeIn-subst{z}
                                   {αcanonh t (fresh avoid :: avoid) ((z , fresh avoid) :: subst-drop z r)}
                                   {var (rename-var r z)} (αcanon-¬freeIn q5 q6) = {!!}



αcanon-completion : ∀{t1 t2 : Tm}{avoid : 𝕃 V}{r : Renaming} → 
--                    (∀ x → freeIn x t1 → list-member _≃_ (rename-var r x)
-- avoid ≡ tt) →
                    renameOk r t1 →  
                    t1 ⟨ ⇛ ⟩ t2 →
                    rename r t2 ⟨ ⇛ ⟩ αcanonh t1 avoid r
αcanon-completion {r = r} rok (⇛var{v}) rewrite rename-var-lem{v}{r} = ⇛var
αcanon-completion r (⇛app d1 d2) = ⇛app (αcanon-completion (substOk-app1 r) d1) (αcanon-completion (substOk-app2 r) d2)
αcanon-completion{ƛ x t}{ƛ x t'}{avoid}{r} rok (⇛lam{x} d) with αcanon-completion{t}{t'}{fresh avoid :: avoid}{subst-drop x r} {!!} d
αcanon-completion{ƛ x t}{ƛ x t'}{avoid}{r} rok (⇛lam{x} d) | p rewrite renaming-to-subst-drop{r}{x} = 
  ⇛alpha{x} p ({!!} , {!!} , q)

--  

 where h : ∀{r : Renaming} →
           all-pred
            (λ p₁ → (fst p₁ ≃ x) ≡ ff → freeIn (fst p₁) t → ¬ freeIn x (snd p₁))
            (map (snd-map var) r) → 
           all-pred
             (λ p₁ → (fst p₁ ≃ x) ≡ ff → freeIn (fst p₁) t → (x ≃ snd p₁) ≡ ff)
             r
       h {[]} u = triv
       h {(a , b) :: r} (u , u') with x ≃ b 
       h {(a , b) :: r} (u , u') | tt = (λ i j → ⊥-elim (u i j refl)) , h{r} u'
       h {(a , b) :: r} (u , u') | ff = (λ i j → refl) , h{r} u'

       q : αcanonh t (fresh avoid :: avoid) ((x , fresh avoid) :: r) ≡
           (< x ↦ fresh avoid >
             αcanonh t (fresh avoid :: avoid)
             (filter (λ p₁ → ~ (fst p₁ ≃ x)) r))
       q with αcanon-rename{t}{x}{(x , fresh avoid) :: r}{fresh avoid :: avoid} {!!} {!!} {!x1!} {!!} {!!}
          
       q | z rewrite ≃-refl{x} | z = refl


αcanon-completion{avoid = avoid}{r} rok (⇛alpha{x}{t2}{t2'}{ƛ y t2''} d (rok' , nf , refl)) = {!!}
  --⇛alpha {y} {t2''} {αcanonh t2'' (fresh avoid :: avoid) ((y , fresh avoid) :: r)} {!!} ({!!} , {!!} , {!!} , {!!} )


