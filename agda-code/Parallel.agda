{- definition of parallel reduction relations, for proof of confluence.
   There is one relation for parallel β, and another for parallel α. -}
open import lib
open import relations
open import diamond
open import VarInterface

module Parallel(vi : VI) where

open VI vi
open import Tm vi
open import Subst vi
open import Beta vi
open import Alpha vi 
open import Tau vi 

----------------------------------------------------------------------
-- parallel beta reduction
----------------------------------------------------------------------

data ⇒ : Tm → Tm → Set where
  ⇒var : ∀{v : V} →
          var v ⟨ ⇒ ⟩ var v
  ⇒app : ∀{t1 t1' t2 t2' : Tm} → 
          t1 ⟨ ⇒ ⟩ t1' →
          t2 ⟨ ⇒ ⟩ t2' →
          (t1 · t2) ⟨ ⇒ ⟩ (t1' · t2')
  ⇒lam : ∀{x : V}{t1 t1' : Tm} →
           t1 ⟨ ⇒ ⟩ t1' →
           (ƛ x t1) ⟨ ⇒ ⟩ (ƛ x t1')
  ⇒beta : ∀{x : V}{t1 t1' t2 t2' c : Tm} → 
           t1 ⟨ ⇒ ⟩ t1' →
           t2 ⟨ ⇒ ⟩ t2' →
           ((ƛ x t1') · t2') ⟨ β ⟩ c → 
           ((ƛ x t1) · t2) ⟨ ⇒ ⟩ c

-- parallel reduction is reflexive
⇒refl : reflexive ⇒ 
⇒refl {var x} = ⇒var
⇒refl {t · t₁} = ⇒app ⇒refl ⇒refl 
⇒refl {ƛ x t} = ⇒lam ⇒refl 

↝β-⇒ : ↝β ⊆ ⇒
↝β-⇒ {(ƛ x t1) · t2}{a'} (τ-base p) = ⇒beta ⇒refl ⇒refl p
↝β-⇒ (τ-app1 x) = ⇒app (↝β-⇒ x) ⇒refl
↝β-⇒ (τ-app2 x) = ⇒app ⇒refl (↝β-⇒ x)
↝β-⇒ (τ-lam x) = ⇒lam (↝β-⇒ x) 

⇒↝β⋆ : ⇒ ⊆ (↝β ⋆)
⇒↝β⋆ ⇒var = ⋆refl 
⇒↝β⋆ (⇒app d d') =  (⋆app1 (⇒↝β⋆ d)) ⋆trans (⋆app2 (⇒↝β⋆ d'))
⇒↝β⋆ (⇒lam d) = ⋆lam (⇒↝β⋆ d)
⇒↝β⋆ (⇒beta d d' b) = (⋆app1 (⋆lam (⇒↝β⋆ d))) ⋆trans ((⋆app2 (⇒↝β⋆ d')) ⋆trans (⋆base (τ-base b)))

⇒-freeIn : ∀{x : V}{t t' : Tm} →
            freeIn x t' →
            t ⟨ ⇒ ⟩ t' →
            freeIn x t
⇒-freeIn f d = ↝β⋆-freeIn f (⇒↝β⋆ d)

⇒-boundIn : ∀{x : V}{t t' : Tm} →
            boundIn x t' →
            t ⟨ ⇒ ⟩ t' →
            boundIn x t
⇒-boundIn f d = ↝β⋆-boundIn f (⇒↝β⋆ d)

⇒-subst : ∀{x : V}{t1 t1' t2 t2' : Tm} →
           t1 ⟨ ⇒ ⟩ t1' →
           t2 ⟨ ⇒ ⟩ t2' →
           bv-apart t2 t1 → 
           ([ t2 / x ] t1) ⟨ ⇒ ⟩ ([ t2' / x ] t1')
⇒-subst {x} {var y}{t2 = t2} {t2'} ⇒var d2 _ with y ≃ x 
⇒-subst {x} {var y}{t2 = t2} {t2'} ⇒var d2 _ | tt = d2
⇒-subst {x} {var y}{t2 = t2} {t2'} ⇒var d2 _ | ff = ⇒var
⇒-subst {x} {(t1a · t1b)} {(t1a' · t1b')} {t2} {t2'} (⇒app d1a d1b) d2 a with bv-apart-app{t2}{t1a}{t1b} a 
⇒-subst {x} {(t1a · t1b)} {(t1a' · t1b')} {t2} {t2'} (⇒app d1a d1b) d2 a | a1 , a2 =
  ⇒app (⇒-subst {x} {t1a} {t1a'} {t2} {t2'} d1a d2 a1) (⇒-subst {x} {t1b} {t1b'} {t2} {t2'} d1b d2 a2)
⇒-subst {x} {ƛ y t1} {ƛ y t1'} {t2} {t2'} (⇒lam d1) d2 a with x ≃ y 
⇒-subst {x} {ƛ y t1} {ƛ y t1'} {t2} {t2'} (⇒lam d1) d2 _ | tt rewrite subst[] t1 | subst[] t1' = ⇒lam d1
⇒-subst {x} {ƛ y t1} {ƛ y t1'} {t2} {t2'} (⇒lam d1) d2 a | ff =
  ⇒lam (⇒-subst{x}{t1}{t1'}{t2}{t2'} d1 d2 λ x f nb → a x f (inj₂ nb)) 
⇒-subst {x} {t1' = c} {t2} {t2'} (⇒beta{y}{t1a}{t1a'}{t1b}{t1b'} d1a d1b ((s , triv), e)) d2 a with keep (x ≃ y)
⇒-subst {x} {t2 = t2} {t2'} (⇒beta{y}{t1a}{t1a'}{t1b}{t1b'} d1a d1b ((s , triv), refl)) d2 a | tt , eq rewrite eq | subst[] t1a =
  ⇒beta{y}{t1a}{t1a'}{[ t2 / x ] t1b}{[ t2' / x ] t1b'} d1a (⇒-subst{x}{t1b}{t1b'}{t2}{t2'} d1b d2 λ x f nb → a x f (inj₂ nb))
    ((subst1ok-compose{t1b'}{t2'}{y}{x}{t1a'} s
       (bv-apart-subst1ok{t2'}{y}{t1a'} (λ x f nb → a x (⇒-freeIn f d2) (inj₁ (inj₂ (⇒-boundIn nb d1a))))) ,
     triv) ,
     h)
  where h : [ t2' / x ] ([ t1b' / y ] t1a') ≡ [ [ t2' / x ] t1b' / y ] t1a'
        h rewrite ≃-≡ eq = subst-same-commute{t1a'}{y}{t2'}{t1b'}
⇒-subst {x} {t2 = t2} {t2'} (⇒beta{y}{t1a}{t1a'}{t1b}{t1b'} d1a d1b ((s , triv), refl)) d2 a | ff , eq rewrite eq =
  ⇒beta {y}
    (⇒-subst {x} {t1a} {t1a'} {t2} {t2'} d1a d2 (λ x f b → a x f (inj₁ (inj₂ b))))
    (⇒-subst {x} {t1b} {t1b'} {t2} {t2'} d1b d2 (λ x f b → a x f (inj₂ b)))
    ((subst1ok-subst{x}{y}{t2'}{t1b'}{t1a'} s
        (bv-apart-subst1ok{t2'}{y}{t1a'}
           (λ x b f → a x (⇒-freeIn {x} {t2} {t2'} b d2) (inj₁ (inj₂ (⇒-boundIn{x}{t1a}{t1a'} f d1a)))))
        ((bv-apart-subst1ok{t2'}{x}{t1b'}
           (λ x b f → a x (⇒-freeIn {x} {t2} {t2'} b d2)
           (inj₂ (⇒-boundIn{x}{t1b}{t1b'} f d1b)))))
        (λ f → a y (⇒-freeIn {y} {t2} {t2'} f d2) (inj₁ (inj₁ ≃-refl)))  ,
      triv) ,
     subst-diff-commute{t1a'}{x}{y}{t2'}{t1b'} eq h1
       (bv-apart-subst1ok{t2'}{x}{t1a'} h2)
       s)
    where h1 : ¬ freeIn y t2'
          h1 f = a y (⇒-freeIn{y}{t2}{t2'} f d2) (inj₁ (inj₁ ≃-refl))
          h2 : bv-apart t2' t1a'
          h2 x f b = a x (⇒-freeIn {x} {t2} {t2'} f d2)
                         (inj₁ (inj₂ (⇒-boundIn {x} {t1a} {t1a'} b d1a)))

----------------------------------------------------------------------
-- parallel alpha reduction
----------------------------------------------------------------------

data ⇛ : Tm → Tm → Set where
  ⇛var : ∀{v : V} →
          var v ⟨ ⇛ ⟩ var v
  ⇛app : ∀{t1 t1' t2 t2' : Tm} → 
          t1 ⟨ ⇛ ⟩ t1' →
          t2 ⟨ ⇛ ⟩ t2' →
          (t1 · t2) ⟨ ⇛ ⟩ (t1' · t2')
  ⇛lam : ∀{x : V}{t1 t1' : Tm} →
           t1 ⟨ ⇛ ⟩ t1' →
           (ƛ x t1) ⟨ ⇛ ⟩ (ƛ x t1')
  ⇛alpha : ∀{x : V}{t1 t1' c : Tm} → 
            t1 ⟨ ⇛ ⟩ t1' →
            (ƛ x t1') ⟨ α ⟩ c → 
            (ƛ x t1) ⟨ ⇛ ⟩ c

⇛refl : reflexive ⇛ 
⇛refl {var x} = ⇛var
⇛refl {t · t₁} = ⇛app ⇛refl ⇛refl 
⇛refl {ƛ x t} = ⇛lam ⇛refl 

↝α-⇛ : ↝α ⊆ ⇛
↝α-⇛ {ƛ x t1}{a'} (τ-base p) = ⇛alpha ⇛refl p
↝α-⇛ (τ-app1 x) = ⇛app (↝α-⇛ x) ⇛refl
↝α-⇛ (τ-app2 x) = ⇛app ⇛refl (↝α-⇛ x)
↝α-⇛ (τ-lam x) = ⇛lam (↝α-⇛ x) 

⇛↝α⋆ : ⇛ ⊆ (↝α ⋆)
⇛↝α⋆ ⇛var = ⋆refl 
⇛↝α⋆ (⇛app d d') =  (⋆app1 (⇛↝α⋆ d)) ⋆trans (⋆app2 (⇛↝α⋆ d'))
⇛↝α⋆ (⇛lam d) = ⋆lam (⇛↝α⋆ d)
⇛↝α⋆ (⇛alpha d a) = (⋆lam (⇛↝α⋆ d)) ⋆trans (⋆base (τ-base a))
