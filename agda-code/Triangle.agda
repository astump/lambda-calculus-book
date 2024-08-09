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

-- idea: might need to define ordering on variables so that we can say fresh (y :: avoid) is bigger than x.
-- Then all variables introduced by αcanonh will also be bigger than x, so we would not capture any
-- occurrence of x when we do αcanonh t (y :: avoid) (subst-drop x r).  

αcanon-rename : ∀{t : Tm}{x y : V}{r : Renaming}{avoid : 𝕃 V} → 
                 all-pred (λ p → fst p ≃ x ≡ ff → freeIn (fst p) t → x ≃ snd p ≡ ff) r →
                 rename-var r x ≡ y → 
                 αcanonh t (y :: avoid) r
              ≡ < x ↦ y > αcanonh t (y :: avoid) (subst-drop x r)
αcanon-rename{var z}{x}{y}{r}{avoid} u rxy rewrite rename-var-lem{rename-var (subst-drop x r) z}{[ x , y ]} = cong var h 
  where
    h' : ∀{r r' : Renaming} →
           z ≃ x ≡ ff → 
           subst-drop x r ≡ r' →
           all-pred (λ p₁ → (fst p₁ ≃ x) ≡ ff → (fst p₁ ≃ z) ≡ tt → (x ≃ snd p₁) ≡ ff) r →
           rename-var r' z ≃ x ≡ ff
    h' {[]} zx eq u rewrite sym eq = zx
    h' {(a , b) :: r} zx eq u with a ≃ x 
    h' {(a , b) :: r} zx eq (_ , u) | tt = h' {r} zx eq u
    h' {(a , b) :: r} zx eq u | ff rewrite sym eq with keep (z ≃ a) 
    h' {(a , b) :: r} zx eq (u , u') | ff | tt , p rewrite p | ≃-≡ p = ~≃-sym (u refl ≃-refl)
    h' {(a , b) :: r} zx eq (u , u') | ff | ff , p rewrite p = h' {r}{filter (λ p₁ → ~ (fst p₁ ≃ x)) r} zx refl u'    

    h : rename-var r z ≡ rename-var [ x , y ] (rename-var (subst-drop x r) z)
    h with keep (z ≃ x) 
    h | tt , p rewrite p | ≃-≡ p | rename-subst-drop1{x}{r} | ≃-refl{x} = rxy
    h | ff , p rewrite p with keep (subst-drop x r) 
    h | ff , p | r' , eq rewrite eq | h'{r} p eq u | sym eq | rename-subst-drop2{x}{z}{r} (~≃-sym p) = refl 
    
αcanon-rename{t1 · t2}{x}{y}{r}{avoid} u rxy
 rewrite αcanon-rename{t1}{x}{y}{r}{avoid} (all-pred-implies (λ u nx fi → u nx (inj₁ fi)) u) rxy
       | αcanon-rename{t2}{x}{y}{r}{avoid} (all-pred-implies (λ u nx fi → u nx (inj₂ fi)) u) rxy = refl


αcanon-rename{ƛ z t}{x}{y}{r}{avoid} u rxy with fst (||-≡-ff{fresh (y :: avoid) ≃ y} (fresh-distinct{y :: avoid}))
αcanon-rename{ƛ z t}{x}{y}{r}{avoid} u rxy | dis rewrite ~≃-sym dis with keep (x ≃ fresh (y :: avoid))
αcanon-rename{ƛ z t}{x}{y}{r}{avoid} u rxy | dis | tt , p
  rewrite p | subst[] (αcanonh t (fresh (y :: avoid) :: y :: avoid)
                       ((z , fresh (y :: avoid)) :: subst-drop x r)) = {!!}
αcanon-rename{ƛ z t}{x}{y}{r}{avoid} u rxy | dis | ff , p rewrite p = {!!}

αcanon-completion : ∀{t1 t2 : Tm}{avoid : 𝕃 V}{r : Renaming} → 
--                    (∀ x → freeIn x t1 → list-member _≃_ (rename-var r x) avoid ≡ tt) →
                    renameOk r t1 →  
                    t1 ⟨ ⇛ ⟩ t2 →
                    rename r t2 ⟨ ⇛ ⟩ αcanonh t1 avoid r
αcanon-completion {r = r} rok (⇛var{v}) rewrite rename-var-lem{v}{r} = ⇛var
αcanon-completion r (⇛app d1 d2) = ⇛app (αcanon-completion (substOk-app1 r) d1) (αcanon-completion {!substOk-app2 r!} d2)
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
       q with αcanon-rename{t}{x}{fresh avoid}{(x , fresh avoid) :: r}{avoid}
          ((λ u → ≃-⊥ u) , h (substOk-lam rok)) (rename-var-immediate{r}{x})
       q | z rewrite ≃-refl{x} = z


αcanon-completion{avoid = avoid}{r} rok (⇛alpha{x}{t2}{t2'}{ƛ y t2''} d (rok' , nf , refl)) = {!!}
  --⇛alpha {y} {t2''} {αcanonh t2'' (fresh avoid :: avoid) ((y , fresh avoid) :: r)} {!!} ({!!} , {!!} , {!!} , {!!} )


