{- compute a list of the free variables of a term -}
open import lib
open import relations
open import VarInterface

module FreeVars(vi : VI) where

open VI vi
open import Tm vi

fv : Tm → 𝕃 V
fv (var x) = [ x ]
fv (t1 · t2) = fv t1 ++ fv t2
fv (ƛ x t) = remove _≃_ x (fv t)

