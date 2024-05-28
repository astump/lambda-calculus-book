open import lib
open import bool-relations

fresh-distinctness : ∀{V : Set}(_≃_ : V → V → 𝔹) → (𝕃 V → V) → Set
fresh-distinctness{V} _≃_ fresh = ∀ {l : 𝕃 V} → all-pred (λ x → x ≃ fresh l ≡ ff) l

record VI : Set₁ where
  field
    V : Set
    _≃_ : V → V → 𝔹
    ≃-equivalence : equivalence _≃_
    ≃-≡ : ∀ {x y : V} → x ≃ y ≡ tt → x ≡ y

  field
    fresh : 𝕃 V → V
    fresh-distinct : ∀ {l : 𝕃 V} → all-pred (λ x → x ≃ fresh l ≡ ff) l --fresh-distinctness _≃_ fresh

  ≃-refl = fst (fst ≃-equivalence)
  ≃-symm = snd ≃-equivalence
  ~≃-symm = ~symmetric _≃_ ≃-symm

----------------------------------------------------------------------
-- an implementation of the above interface based on V = ℕ

fresh-ℕ : 𝕃 ℕ → ℕ
fresh-ℕ l = (foldr _+_ 1 l)

fresh-ℕ-suc : ∀{l : 𝕃 ℕ} → Σ[ y ∈ ℕ ] fresh-ℕ l ≡ suc y
fresh-ℕ-suc {[]} = 0 , refl
fresh-ℕ-suc {x :: l} with fresh-ℕ-suc {l}
fresh-ℕ-suc {x :: l} | y , p rewrite p rewrite +suc x y = x + y , refl

fresh-ℕ-step : ∀{x : ℕ}{l1 l2 : 𝕃 ℕ} → x < fresh-ℕ (l1 ++ x :: l2) ≡ tt
fresh-ℕ-step {x} {[]}{l2} with fresh-ℕ-suc{l2} 
fresh-ℕ-step {x} {[]} | y , r rewrite r | +suc x y = ≤<suc{x} (≤+1 x y)
fresh-ℕ-step {x} {x₁ :: l1}{l2} with fresh-ℕ-step{x}{l1}{l2}
fresh-ℕ-step {x} {x₁ :: l1} | r = <+1{x}{x₁} r

fresh-ℕ-distinct : ∀{l1 l2 : 𝕃 ℕ} → all-pred (λ x → x =ℕ fresh-ℕ (l1 ++ l2) ≡ ff) l2
fresh-ℕ-distinct {l1} {[]} = triv
fresh-ℕ-distinct {l1} {x :: l2} = <-not-=ℕ'{x} (fresh-ℕ-step{x}{l1}{l2}) , h
 where h : all-pred (λ x₁ → x₁ =ℕ fresh-ℕ (l1 ++ x :: l2) ≡ ff) l2
       h rewrite sym (++-singleton x l1 l2) = fresh-ℕ-distinct{l1 ++ [ x ]}{l2}

VI-ℕ : VI
VI-ℕ = record {
        V = ℕ ;
        _≃_ = _=ℕ_ ;
        ≃-equivalence = =ℕ-equivalence ;
        ≃-≡ = =ℕ-to-≡ ;
        fresh = fresh-ℕ ;
        fresh-distinct = fresh-ℕ-distinct{[]}}