## Relating list-indexed lists

```
module VecPointwise2 where

open import Utils

import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any as Any
```

This is used by handlers, which contain list-indexed lists.

Pointwise lifting of relations between elements of two list-indexed lists `All F as` and `All G bs`.
TODO: hide this?
```
module _ {A B : Set} {F : A → Set} {G : B → Set} (R : ∀ {a b} → F a → G b → Set) where

  data All₂ : ∀ {as bs} → All F as → All G bs → Set where
    [] : All₂ [] []
    _∷_ : ∀ {a b as bs} {x : F a} {y : G b} {xs : All F as} {ys : All G bs} → R x y → All₂ xs ys → All₂ (x ∷ xs) (y ∷ ys)

module _ {A B : Set} {F : A → Set} {G : B → Set} {R : ∀ {a b} → F a → G b → Set} where

  lookup-All₂ : ∀ {as bs} {xs : All F as} {ys : All G bs} {a}
    → (a∈as : a ∈ as)
    → All₂ R xs ys
    → Σ[ b ∈ B ] Σ[ b∈bs ∈ b ∈ bs ] R (All.lookup xs a∈as) (All.lookup ys b∈bs)
  lookup-All₂ (here refl) (r ∷ rs) = _ , here refl , r
  lookup-All₂ (there a∈as) (r ∷ rs)
    with lookup-All₂ a∈as rs
  ... | _ , b∈bs , r = _ , there b∈bs , r

-- | Specialization of All₂ that equates the two underlying lists.
module _ {A : Set} {F G : A → Set} (R : ∀ {a} → F a → G a → Set) where
  All₂′ : ∀  {as bs} → All F as → All G bs → Set
  All₂′ = All₂ λ {a} {b} x y → Σ (a ≡ b) λ{ refl → R x y }

module _ {A : Set} ⦃ DecEq-A : DecEq A ⦄ {F G : A → Set} {R : ∀ {a} → F a → G a → Set} where
  open import Data.Fin.Base using (toℕ)
  open import Data.Nat.Properties using (suc-injective)

  lookup-All₂′-index : ∀ {as bs} {xs : All F as} {ys : All G bs} {a}
      → (a∈as : a ∈ as)
      → (rs : All₂′ R xs ys)
      → let b , b∈bs , _ = lookup-All₂ a∈as rs in
        toℕ (Any.index a∈as) ≡ toℕ (Any.index b∈bs)
  lookup-All₂′-index (here refl) (_∷_ (refl , r) rs) = refl
  lookup-All₂′-index (there a∈as) (_∷_ (refl , r) rs)
    = cong suc (lookup-All₂′-index a∈as rs)

  idem-index : ∀ {as} {a : A} {a∈as a∈as′ : a ∈ as} → toℕ (Any.index a∈as) ≡ toℕ (Any.index a∈as′) → a∈as ≡ a∈as′
  idem-index {a∈as = here refl} {a∈as′ = here refl} _ = refl
  idem-index {a∈as = there a∈as} {a∈as′ = there a∈as′} suc-eq = cong there (idem-index (suc-injective suc-eq))

  All₂′-≡ : ∀ {as bs} {xs : All F as} {ys : All G bs} → All₂′ R xs ys → as ≡ bs
  All₂′-≡ [] = refl
  All₂′-≡ ((refl , _) ∷ rs) with All₂′-≡ rs
  ... | refl = refl

  lookup-All₂′-∈? : ∀ {as bs} {xs : All F as} {ys : All G bs} {a}
      → {a∈as : a ∈ as}
      → (rs : All₂′ R xs ys)
      → let b , b∈bs , _ = lookup-All₂ a∈as rs in
        (a ∈? as) ≡ yes a∈as → (b ∈? bs) ≡ yes b∈bs
  lookup-All₂′-∈? {a∈as = a∈as} rs eq with All₂′-≡ rs | lookup-All₂ a∈as rs | lookup-All₂′-index a∈as rs
  ... | refl | _ , _ , refl , _ | eq′ = trans eq (cong yes (idem-index eq′))

  lookup-All₂′ : ∀ {as bs} {xs : All F as} {ys : All G bs} {a}
    → {a∈as : a ∈ as}
    → All₂′ R xs ys
    → (a ∈? as) ≡ yes a∈as
    → Σ[ a∈bs ∈ a ∈ bs ] (a ∈? bs) ≡ yes a∈bs × R (All.lookup xs a∈as) (All.lookup ys a∈bs)
  lookup-All₂′ {a∈as = a∈as} rs eq with lookup-All₂ a∈as rs | lookup-All₂′-∈? rs eq
  ... | _ , a∈bs , refl , r | eq′ = a∈bs , eq′ , r
```
