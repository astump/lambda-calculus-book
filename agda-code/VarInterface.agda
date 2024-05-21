open import lib
open import bool-relations

record VI : Set₁ where
  field
    V : Set
    _≃_ : V → V → 𝔹
    ≃-equivalence : equivalence _≃_
    ≃-≡ : ∀ {x y : V} → x ≃ y ≡ tt → x ≡ y

  ≃-refl = fst (fst ≃-equivalence)
  ≃-symm = snd ≃-equivalence
  ~≃-symm = ~symmetric _≃_ ≃-symm