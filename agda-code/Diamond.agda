{- -}
open import lib
open import relations
open import diamond
open import VarInterface

module Diamond(vi : VI) where

open VI vi
open import Tm vi
open import Subst vi
open import Beta vi
open import Alpha vi 
open import FreeVars vi 
open import Parallel vi
open import Triangle vi 

diamond-⇒ : diamond ⇒
diamond-⇒ = {!!}

confluent-↝αβ : confluent ↝αβ
confluent-↝αβ = mediator-diamond ↝αβ-⇒ ⇒-↝αβ⋆ diamond-⇒