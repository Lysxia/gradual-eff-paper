# Gradual Guarantee

## Precision on terms

Simple Blame Calculus with proof relevant casts.
Uses polarity to unify upcasts and downcasts.
Uses nested evaluation contexts.

Siek, Thiemann, and Wadler

```
module Prec where

open import Utils
open import Type
open import Core as Core hiding (On-Perform)
open import Progress

import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any as Any
```


## Precision on contexts

```
infix 4 _≤ᴳ_
infixl 5 _⹁_

data _≤ᴳ_ : Context → Context → Set where

  ∅ :
      ------
      ∅ ≤ᴳ ∅

  _⹁_ : ∀{Γ Γ′ A A′}
    → Γ ≤ᴳ Γ′
    → A ≤ A′
      ------------------
    → Γ ⹁ A ≤ᴳ Γ′ ⹁ A′

private variable
  Γ Γ′ Δ Δ′ : Context
  Γ≤ : Γ ≤ᴳ Γ′
  Δ≤ : Δ ≤ᴳ Δ′
  P P′ Q Q′ : Typeᶜ
  A A′ B B′ C : Type
  E E′ F F′ : Effs
  P≤ : P ≤ᶜ P′
  Q≤ : Q ≤ᶜ Q′
  A≤ : A ≤ A′
  B≤ : B ≤ B′
  E≤ : E ≤ᵉ E′
  F≤ : F ≤ᵉ F′
```

## Reflexivity and transitivity of context precision

```
idᴳ : ∀ {Γ} → Γ ≤ᴳ Γ
idᴳ {∅}      =  ∅
idᴳ {Γ ⹁ A}  =  idᴳ ⹁ id

_⨟ᴳ_ : ∀ {Γ Γ′ Γ″} → Γ ≤ᴳ Γ′ → Γ′ ≤ᴳ Γ″ → Γ ≤ᴳ Γ″
∅ ⨟ᴳ ∅                    =  ∅
(Γ≤ ⹁ A≤) ⨟ᴳ (Γ′≤ ⹁ A′≤)  =  (Γ≤ ⨟ᴳ Γ′≤) ⹁ (A≤ ⨟ A′≤)

left-idᴳ : ∀ {Γ Δ} → (Γ≤Δ : Γ ≤ᴳ Δ) → idᴳ ⨟ᴳ Γ≤Δ ≡ Γ≤Δ
left-idᴳ ∅ = refl
left-idᴳ (Γ≤Δ ⹁ p) rewrite left-idᴳ Γ≤Δ | left-id p = refl

right-idᴳ : ∀ {Γ Δ} → (Γ≤Δ : Γ ≤ᴳ Δ) → Γ≤Δ ⨟ᴳ idᴳ ≡ Γ≤Δ
right-idᴳ ∅ = refl
right-idᴳ (Γ≤Δ ⹁ p) rewrite right-idᴳ Γ≤Δ | right-id p = refl
```

## Precision on variables

```
infix 3 _⊢_≤ˣ_⦂_

data _⊢_≤ˣ_⦂_ : ∀ {Γ Γ′ A A′} → Γ ≤ᴳ Γ′ → Γ ∋ A → Γ′ ∋ A′ → A ≤ A′ → Set where

  Z≤Z : ∀ {Γ Γ′ A A′} {Γ≤ : Γ ≤ᴳ Γ′} {A≤ : A ≤ A′}
      ----------------------
    → Γ≤ ⹁ A≤ ⊢ Z ≤ˣ Z ⦂ A≤

  S≤S : ∀ {Γ Γ′ A A′ B B′ x x′} {Γ≤ : Γ ≤ᴳ Γ′} {A≤ : A ≤ A′} {B≤ : B ≤ B′}
    → Γ≤ ⊢ x ≤ˣ x′ ⦂ A≤ 
      ---------------------------
    → Γ≤ ⹁ B≤ ⊢ S x ≤ˣ S x′ ⦂ A≤

```

## Commuting diagram

```
commute≤ : ∀ {A B C} (±p : A => B) (q : B ≤ C) (r : A ≤ C) → Set
commute≤ (+ p) q r  =  p ⨟ q ≡ r
commute≤ (- p) q r  =  p ⨟ r ≡ q

≤commute : ∀ {A B C} (p : A ≤ B) (±q : B => C) (r : A ≤ C) → Set
≤commute p (+ q) r  =  p ⨟ q ≡ r
≤commute p (- q) r  =  r ⨟ q ≡ p
```

```
commute≤ᵉ : ∀ {A B C} (±p : A =>ᵉ B) (q : B ≤ᵉ C) (r : A ≤ᵉ C) → Set
{-
commute≤ᵉ id q r  =  q ≡ r
commute≤ᵉ +☆ q r  =  ⊤  -- TODO
commute≤ᵉ -☆ q r  =  ⊤  -- TODO
-}
commute≤ᵉ p q r  =  ⊤

≤commuteᵉ : ∀ {A B C} (p : A ≤ᵉ B) (±q : B =>ᵉ C) (r : A ≤ᵉ C) → Set
≤commuteᵉ p q r   =  ⊤  -- TODO
```

```
commute≤ᶜ : ∀ {P Q R} (±p : P =>ᶜ Q) (q : Q ≤ᶜ R) (r : P ≤ᶜ R) → Set
commute≤ᶜ (⟨ ±pᵉ ⟩ ±pᵛ) (⟨ qᵉ ⟩ qᵛ) (⟨ rᵉ ⟩ rᵛ)  =  commute≤ᵉ ±pᵉ qᵉ rᵉ × commute≤ ±pᵛ qᵛ rᵛ

≤commuteᶜ : ∀ {A B C} (p : A ≤ᶜ B) (±q : B =>ᶜ C) (r : A ≤ᶜ C) → Set
≤commuteᶜ (⟨ pᵉ ⟩ pᵛ) (⟨ ±qᵉ ⟩ ±qᵛ) (⟨ rᵉ ⟩ rᵛ)  =  ≤commuteᵉ pᵉ ±qᵉ rᵉ × ≤commute pᵛ ±qᵛ rᵛ
```

## Lemmas about commuting diagrams

```
drop⇑ : ∀ {A B G} {±p : A => B} {q : B ≤ G} {r : A ≤ G} {g : Ground G}
  → commute≤ ±p (q ⇑ g) (r ⇑ g)
    ---------------------------
  → commute≤ ±p q r
drop⇑ {±p = + _} refl = refl
drop⇑ {±p = - _} refl = refl

ident≤ : ∀ {A B} {q r : A ≤ B}
  → (±p : A => A)
  → split ±p ≡ id
  → commute≤ ±p q r
    -----
  → q ≡ r
ident≤ {q = q} (+ id) refl refl rewrite left-id q = refl
ident≤ {r = r} (- id) refl refl rewrite left-id r = refl

≤ident : ∀ {A B} {p r : A ≤ B}
  → (±q : B => B)
  → split ±q ≡ id
  → ≤commute p ±q r
    -----
  → p ≡ r
≤ident (+ id) refl refl = refl
≤ident (- id) refl refl = refl

dom≤ :  ∀ {A A′ A″ P P′ P″}
    {±p : A ⇒ P => A′ ⇒ P′} {q : A′ ⇒ P′ ≤ A″ ⇒ P″} {r : A ⇒ P ≤ A″ ⇒ P″}
    {∓s : A′ => A} {±t : P =>ᶜ P′}
  → split ±p ≡ ∓s ⇒ ±t
  → commute≤ ±p q r
    ---------------------------
  → commute≤ ∓s (dom r) (dom q)
dom≤ {±p = + s ⇒ t} {q = q} refl refl = dom-⨟ (s ⇒ t) q
dom≤ {±p = - s ⇒ t} {r = r} refl refl = dom-⨟ (s ⇒ t) r

cod≤ :  ∀ {A A′ A″ P P′ P″}
    {±p : A ⇒ P => A′ ⇒ P′} {q : A′ ⇒ P′ ≤ A″ ⇒ P″} {r : A ⇒ P ≤ A″ ⇒ P″}
    {∓s : A′ => A} {±t : P =>ᶜ P′}
  → split ±p ≡ ∓s ⇒ ±t
  → commute≤ ±p q r
    ---------------------------
  → commute≤ᶜ ±t (cod q) (cod r)
cod≤ {±p = + s ⇒ t} {q = q} refl refl = tt , cong _≤ᶜ_.returns (cod-⨟ (s ⇒ t) q)
cod≤ {±p = - s ⇒ t} {r = r} refl refl = tt , cong _≤ᶜ_.returns (cod-⨟ (s ⇒ t) r)

≤dom :  ∀ {A A′ A″ B B′ B″}
    {p : A ⇒ B ≤ A′ ⇒ B′} {±q : A′ ⇒ B′ => A″ ⇒ B″} {r : A ⇒ B ≤ A″ ⇒ B″}
    {∓s : A″ => A′} {±t : B′ =>ᶜ B″}
  → split ±q ≡ ∓s ⇒ ±t
  → ≤commute p ±q r
    ---------------------------
  → ≤commute (dom r) ∓s (dom p)
≤dom {p = p} {±q = + s ⇒ t} {r = r} refl refl = dom-⨟ p (s ⇒ t)
≤dom {p = p} {±q = - s ⇒ t} {r = r} refl refl = dom-⨟ r (s ⇒ t)

≤cod :  ∀ {A A′ A″ B B′ B″}
    {p : A ⇒ B ≤ A′ ⇒ B′} {±q : A′ ⇒ B′ => A″ ⇒ B″} {r : A ⇒ B ≤ A″ ⇒ B″}
    {∓s : A″ => A′} {±t : B′ =>ᶜ B″}
  → split ±q ≡ ∓s ⇒ ±t
  → ≤commute p ±q r
    ---------------------------
  → ≤commuteᶜ (cod p) ±t (cod r)
≤cod {p = p} {±q = + s ⇒ t} refl refl = tt , cong _≤ᶜ_.returns (cod-⨟ p (s ⇒ t))
≤cod {±q = - s ⇒ t} {r = r} refl refl = tt , cong _≤ᶜ_.returns (cod-⨟ r (s ⇒ t))
```

## Precision on terms

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

```
infix 3 _⊢_≤ᴹ_⦂_ _⊢_≤_⦂_➡_

record _⊢_≤_⦂_➡_ {Γ Γ′} (Γ≤ : Γ ≤ᴳ Γ′) {P P′ Q Q′} (H : Γ ⊢ P ➡ Q) (H′ : Γ′ ⊢ P′ ➡ Q′) (P≤ : P ≤ᶜ P′) (Q≤ : Q ≤ᶜ Q′) : Set

data _⊢_≤ᴹ_⦂_ {Γ Γ′} (Γ≤ : Γ ≤ᴳ Γ′) : ∀ {A A′} → Γ ⊢ A → Γ′ ⊢ A′ → A ≤ᶜ A′ → Set where

  `≤` : ∀ {A A′ x x′ E E′} {pᵉ : E ≤ᵉ E′} {p : A ≤ A′}
    → Γ≤ ⊢ x ≤ˣ x′ ⦂ p
      --------------------
    → Γ≤ ⊢ ` x ≤ᴹ ` x′ ⦂ ⟨ pᵉ ⟩ p

  ƛ≤ƛ : ∀ {E E′ A A′ B B′ N N′} {pᵉ : E ≤ᵉ E′} {p : A ⇒ B ≤ A′ ⇒ B′}
    → Γ≤ ⹁ dom p ⊢ N ≤ᴹ N′ ⦂ cod p
      ----------------------------
    → Γ≤ ⊢ ƛ N ≤ᴹ ƛ N′ ⦂ ⟨ pᵉ ⟩ p

  ·≤· : ∀ {A A′ E E′ B B′ L L′ M M′} {p : A ⇒ ⟨ E ⟩ B ≤ A′ ⇒ ⟨ E′ ⟩ B′} 
      (let qᵉ = _≤ᶜ_.effects (cod p))
    → Γ≤ ⊢ L ≤ᴹ L′ ⦂ ⟨ qᵉ ⟩ p
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ qᵉ ⟩ dom p
      -----------------------------
    → Γ≤ ⊢ L · M ≤ᴹ L′ · M′ ⦂ cod p

  $≤$ : ∀ {ι E E′} {pᵉ : E ≤ᵉ E′}
    → (k : rep ι)
      ------------------------
    → Γ≤ ⊢ $ k ≤ᴹ $ k ⦂ ⟨ pᵉ ⟩ id

  ⦅⦆≤⦅⦆ : ∀ {ι ι′ ι″ E E′ M M′ N N′} {pᵉ : E ≤ᵉ E′}
    → (_⊕_ : rep ι → rep ι′ → rep ι″)
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ pᵉ ⟩ id
    → Γ≤ ⊢ N ≤ᴹ N′ ⦂ ⟨ pᵉ ⟩ id
      -------------------------------------
    → Γ≤ ⊢ M ⦅ _⊕_ ⦆ N ≤ᴹ M′ ⦅ _⊕_ ⦆ N′ ⦂ ⟨ pᵉ ⟩ id
    
  ⇑≤⇑ : ∀ {G E E′ M M′} {pᵉ : E ≤ᵉ E′}
    → (g : Ground G)
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ pᵉ ⟩ id
      -----------------------------
    → Γ≤ ⊢ (M ⇑ g) ≤ᴹ (M′ ⇑ g) ⦂ ⟨ pᵉ ⟩ id

  ≤⇑ : ∀ {A G E E′ M M′} {p : A ≤ G} {pᵉ : E ≤ᵉ E′}
    → (g : Ground G)
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ pᵉ ⟩ p
      --------------------------
    → Γ≤ ⊢ M ≤ᴹ (M′ ⇑ g) ⦂ ⟨ pᵉ ⟩ (p ⇑ g)

  ▷≤ : ∀ {E E′ A B C} {M : Γ ⊢ ⟨ E ⟩ A} {M′ : Γ′ ⊢ ⟨ E′ ⟩ C} {pᵉ : E ≤ᵉ E′}
          {±p : A => B} {q : B ≤ C} {r : A ≤ C}
    → commute≤ ±p q r
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ pᵉ ⟩ r
      -------------------------
    → Γ≤ ⊢ (M ▷ ±p) ≤ᴹ M′ ⦂ ⟨ pᵉ ⟩ q

  ≤▷ : ∀ {E E′ A B C} {M : Γ ⊢ ⟨ E ⟩ A} {M′ : Γ′ ⊢ ⟨ E′ ⟩ B} {pᵉ : E ≤ᵉ E′}
          {p : A ≤ B} {±q : B => C} {r : A ≤ C}
    → ≤commute p ±q r
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ pᵉ ⟩ p
      -------------------------
    → Γ≤ ⊢ M ≤ᴹ (M′ ▷ ±q) ⦂ ⟨ pᵉ ⟩ r

  ⟨⟩≤ : ∀ {E E′ F A A′} {A≤ : A ≤ A′} {E≤ : E ≤ᵉ E′} {F≤ : F ≤ᵉ E′}
      {±p : F =>ᵉ E} {M M′}
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ F≤ ⟩ A≤
    → Γ≤ ⊢ M ▷⟨ ±p ⟩ ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ A≤

  ≤⟨⟩ : ∀ {E E′ F′ A A′} {A≤ : A ≤ A′} {E≤ : E ≤ᵉ E′} {F≤ : E ≤ᵉ F′}
      {±p : F′ =>ᵉ E′} {M M′}
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ F≤ ⟩ A≤
    → Γ≤ ⊢ M ≤ᴹ M′ ▷⟨ ±p ⟩ ⦂ ⟨ E≤ ⟩ A≤

  blame≤ : ∀ {A A′ M′} {p : A ≤ᶜ A′}
      ---------------------
    → Γ≤ ⊢ blame ≤ᴹ M′ ⦂ p

  wrap≤ : ∀ {A A′ A″ B B′ B″ E E′}
             {N : Γ ⹁ A ⊢ B} {N′ : Γ′ ⹁ A″ ⊢ B″}
             {E≤ : E ≤ᵉ E′}
             {±p : A ⇒ B => A′ ⇒ B′} {q : A′ ⇒ B′ ≤ A″ ⇒ B″} {r : A ⇒ B ≤ A″ ⇒ B″}
             {∓s : A′ => A} {±t : B =>ᶜ B′}
    → split ±p ≡ ∓s ⇒ ±t
    → commute≤ ±p q r
    → (∀ {F F′} {F≤ : F ≤ᵉ F′} → Γ≤ ⊢ ƛ N ≤ᴹ ƛ N′ ⦂ ⟨ F≤ ⟩ r)
      -----------------------------------------------------
    → Γ≤ ⊢ ƛ-wrap ∓s ±t (ƛ N) ≤ᴹ ƛ N′ ⦂ ⟨ E≤ ⟩ q

  ≤wrap : ∀ {A A′ A″ B B′ B″ E E′}
             {N : Γ ⹁ A ⊢ B} {N′ : Γ′ ⹁ A′ ⊢ B′}
             {E≤ : E ≤ᵉ E′}
             {p : A ⇒ B ≤ A′ ⇒ B′} {±q : A′ ⇒ B′ => A″ ⇒ B″} {r : A ⇒ B ≤ A″ ⇒ B″}
             {∓s : A″ => A′} {±t : B′ =>ᶜ B″}
    → split ±q ≡ ∓s ⇒ ±t
    → ≤commute p ±q r
    → (∀ {F F′} {F≤ : F ≤ᵉ F′} → Γ≤ ⊢ ƛ N ≤ᴹ ƛ N′ ⦂ ⟨ F≤ ⟩ p)
      -----------------------------------------------------
    → Γ≤ ⊢ ƛ N ≤ᴹ ƛ-wrap ∓s ±t (ƛ N′) ⦂ ⟨ E≤ ⟩ r

  perform≤perform : ∀ {E E′ e} {e∈E : e ∈☆ E} {e∈E′ : e ∈☆ E′} {A}
                      {E≤ : E ≤ᵉ E′} {M M′}
    → {eq : response e ≡ A}
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ id
    → Γ≤ ⊢ perform- e∈E eq M ≤ᴹ perform- e∈E′ eq M′ ⦂ ⟨ E≤ ⟩ id

  handle≤handle : ∀ {P P′ Q Q′} {P≤ : P ≤ᶜ P′} {Q≤ : Q ≤ᶜ Q′} {H H′ M M′}
    → Γ≤ ⊢ H ≤ H′ ⦂ P≤ ➡ Q≤
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ P≤
    → Γ≤ ⊢ handle H M ≤ᴹ handle H′ M′ ⦂ Q≤

On-Perform : ∀ {Γ Γ′} (Γ≤ : Γ ≤ᴳ Γ′) {Q Q′} (Q≤ : Q ≤ᶜ Q′) → ∀ {Eh Eh′}
  → Core.On-Perform Γ Q Eh → Core.On-Perform Γ′ Q′ Eh′ → Set
On-Perform Γ≤ Q≤ = All₂′ λ M M′ → ∃[ B⇒Q≤ ] dom B⇒Q≤ ≡ id × cod B⇒Q≤ ≡ Q≤ × (Γ≤ ⹁ id ⹁ (B⇒Q≤) ⊢ M ≤ᴹ M′ ⦂ Q≤)

record _⊢_≤_⦂_➡_ Γ≤ {P P′ Q Q′} H H′ P≤ Q≤ where
  inductive
  open _≤ᶜ_ using (returns)
  field
    on-return : Γ≤ ⹁ returns P≤ ⊢ on-return H ≤ᴹ on-return H′ ⦂ Q≤
    on-perform : On-Perform Γ≤ Q≤ (on-perform H) (on-perform H′)

open _⊢_≤_⦂_➡_ public
```

```
generalize-ƛ≤ƛ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᴳ Γ′} {A A′} {P P′} {p : A ⇒ P ≤ A′ ⇒ P′} {N : Γ ⹁ A ⊢ P} {N′}
  → ∀ {E E′ F F′} {E≤ : E ≤ᵉ E′} {F≤ : F ≤ᵉ F′}
  → Γ≤ ⊢ (ƛ N) ≤ᴹ (ƛ N′) ⦂ ⟨ E≤ ⟩ p
  → Γ≤ ⊢ (ƛ N) ≤ᴹ (ƛ N′) ⦂ ⟨ F≤ ⟩ p
generalize-ƛ≤ƛ (ƛ≤ƛ N≤N′) = ƛ≤ƛ N≤N′
generalize-ƛ≤ƛ (wrap≤ i e N≤N′) = wrap≤ i e N≤N′
generalize-ƛ≤ƛ (≤wrap i e N≤N′) = ≤wrap i e N≤N′
```

## Upcast congruence

```
data _=>_∋_≤_ : ∀ {P P′ Q Q′} → P ≤ᶜ P′ → Q ≤ᶜ Q′ → P =>ᵉᵛ Q → P′ =>ᵉᵛ Q′ → Set where
  -- _≤+ᵛ_ :
  --   (A≤ : A ≤ B) → (A′≤ : A′ ≤ B′) → (⟨-⟩_ {E = E} (+ A≤)) ≤ᵏ ⟨-⟩_ {E = E′} (+ A′≤)
  -- _≤-ᵛ_ :
  --   (B≤ : B ≤ A) → (B′≤ : B′ ≤ A′) → (⟨-⟩_ {E = E} (- B≤)) ≤ᵏ ⟨-⟩_ {E = E′} (- B′≤)
  +ᵉ :
      (E≤F : E ≤ᵉ F) → (E′≤F′ : E′ ≤ᵉ F′)
    → (⟨ E≤ ⟩ A≤) => (⟨ F≤ ⟩ A≤) ∋ ⟨_⟩- (+ E≤F) ≤ ⟨_⟩- (+ E′≤F′)
  -ᵉ :
      (F≤E : F ≤ᵉ E) → (F′≤E′ : F′ ≤ᵉ E′) → (⟨ E≤ ⟩ A≤) => (⟨ F≤ ⟩ A≤) ∋ ⟨_⟩- (- F≤E) ≤ ⟨_⟩- (- F′≤E′)
```

```
+≤+ : ∀ {Γ Γ′ E E′ A B A′ B′} {M : Γ ⊢ ⟨ E ⟩ A} {M′ : Γ′ ⊢ ⟨ E′ ⟩ A′} {Γ≤ : Γ ≤ᴳ Γ′}
    {pᵉ : E ≤ᵉ E′} {p : A ≤ B} {q : A′ ≤ B′} {s : A ≤ A′} {t : B ≤ B′}
  → p ⨟ t ≡ s ⨟ q
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ pᵉ ⟩ s
    ------------------------------------
  → Γ≤ ⊢ (M ▷ (+ p)) ≤ᴹ (M′ ▷ (+ q)) ⦂ ⟨ pᵉ ⟩ t
+≤+ e M≤M′ = ▷≤ e (≤▷ refl M≤M′)
```

Here is the derivation:

    Γ≤ ⊢ M ≤ᴹ M′ ⦂ s
    s ⨟ q ≡ r
    ---------------------- ≤+
    Γ≤ ⊢ M ≤ᴹ (M′ + q) ⦂ r
    p ⨟ t ≡ r
    ---------------------------- +≤
    Γ≤ ⊢ (M + p) ≤ᴹ (M′ + q) ⦂ t

Here it is illustrated:

                   s
         M : A    ---→    M′ : A′
           |       \         |
         p |      r \        | q
           -         ↘       -
      (M + p) : B ---→ (M′ + q) : B′
                   t


## Downcast congruence

```
-≤- : ∀ {Γ Γ′ E E′ A B A′ B′} {M : Γ ⊢ ⟨ E ⟩ B} {M′ : Γ′ ⊢ ⟨ E′ ⟩ B′} {Γ≤ : Γ ≤ᴳ Γ′}
    {pᵉ : E ≤ᵉ E′} {p : A ≤ B} {q : A′ ≤ B′} {s : A ≤ A′} {t : B ≤ B′}
  → s ⨟ q ≡ p ⨟ t
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ pᵉ ⟩ t
    ------------------------------------
  → Γ≤ ⊢ (M ▷ (- p)) ≤ᴹ (M′ ▷ (- q)) ⦂ ⟨ pᵉ ⟩ s
-≤- e M≤M′ = ≤▷ e (▷≤ refl M≤M′)
```

Here is the derivation:

    Γ≤ ⊢ M ≤ᴹ M′ ⦂ t
    p ⨟ t ≡ r
    ---------------------- ≤+
    Γ≤ ⊢ (M - p) ≤ᴹ M′ ⦂ r
    s ⨟ q ≡ r
    ---------------------------- +≤
    Γ≤ ⊢ (M - p) ≤ᴹ (M′ - q) ⦂ t

Here it is illustrated:

                   s
         M : A    ---→    M′ : A′
           |       \         |
         p |      r \        | q
           -         ↘       -
      (M + p) : B ---→ (M′ + q) : B′
                   t

## Effect cast congruence

```
=>-≤ : ∀ {M : Γ ⊢ P} {M′ : Γ′ ⊢ P′} {P=>Q P′=>Q′}
  → P≤ => Q≤ ∋ P=>Q ≤ P′=>Q′
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ P≤
    ------------------------------------
  → Γ≤ ⊢ (M ▷⟨⟩ P=>Q) ≤ᴹ (M′ ▷⟨⟩ P′=>Q′) ⦂ Q≤
=>-≤ (+ᵉ {F≤ = F≤} E≤F E′≤F′) M≤M′ = ⟨⟩≤ {F≤ = E≤F ⨟ᵉ F≤} (≤⟨⟩ M≤M′)
=>-≤ (-ᵉ {E≤ = E≤} F≤E F′≤E′) M≤M′ = ≤⟨⟩ {F≤ = F≤E ⨟ᵉ E≤} (⟨⟩≤ M≤M′)
```

## Reflexivity of term precision

```
reflˣ : ∀ {Γ A}
    → (x : Γ ∋ A)
      -------------------
    → idᴳ ⊢ x ≤ˣ x ⦂ id
reflˣ Z      =  Z≤Z
reflˣ (S x)  =  S≤S (reflˣ x)

reflʰ : ∀ {Γ P Q}
  → (H : Γ ⊢ P ➡ Q)
  → idᴳ ⊢ H ≤ H ⦂ ⟨ id ⟩ id ➡ ⟨ id ⟩ id

reflᴹ : ∀ {Γ P}
    → (M : Γ ⊢ P)
      -------------------
    → idᴳ ⊢ M ≤ᴹ M ⦂ ⟨ id ⟩ id
reflᴹ (` x)          =  `≤` (reflˣ x)
reflᴹ (ƛ M)          =  ƛ≤ƛ (reflᴹ M)
reflᴹ (L · M)        =  ·≤· (reflᴹ L) (reflᴹ M)
reflᴹ ($ k)          =  $≤$ k
reflᴹ (M ⦅ _⊕_ ⦆ N)  =  ⦅⦆≤⦅⦆ _⊕_ (reflᴹ M) (reflᴹ N)
reflᴹ (M ⇑ g)        =  ⇑≤⇑ g (reflᴹ M)
reflᴹ (M ▷ (+ p))    =  +≤+ (sym (left-id p)) (reflᴹ M)
reflᴹ (M ▷ (- p))    =  -≤- (left-id p) (reflᴹ M)
reflᴹ blame          =  blame≤
reflᴹ (M ▷⟨ + p ⟩)   = =>-≤ (+ᵉ p p) (reflᴹ M)
reflᴹ (M ▷⟨ - p ⟩)   = =>-≤ (-ᵉ p p) (reflᴹ M)
reflᴹ (perform- e∈E eq M) = perform≤perform (reflᴹ M)
reflᴹ (handle H M) = handle≤handle (reflʰ H) (reflᴹ M)

reflʰ H = record
  { on-return = reflᴹ (H .on-return)
  ; on-perform = refl-on-perform (H .on-perform) }
  where
    refl-on-perform : ∀ {Eh} Ms → On-Perform _ _ {Eh = Eh} Ms Ms
    refl-on-perform [] = []
    refl-on-perform (M ∷ Ms) = (refl , id , refl , refl , reflᴹ M) ∷ refl-on-perform Ms
```

## Renaming {#renaming-prec}

Precision on renamings

```
infix 4 _→ᴿ_∋_≤_ _→ˢ_∋_≤_ _→ᵀ_∋_≤_

_→ᴿ_∋_≤_ : ∀ {Γ Γ′ Δ Δ′} (Γ≤ : Γ ≤ᴳ Γ′) (Δ≤ : Δ ≤ᴳ Δ′) → (Γ →ᴿ Δ) → (Γ′ →ᴿ Δ′) → Set
Γ≤ →ᴿ Δ≤ ∋ ρ ≤ ρ′ = ∀ {A A′} {A≤ : A ≤ A′} {x x′}
  → Γ≤ ⊢ x ≤ˣ x′ ⦂ A≤
    -----------------------
  → Δ≤ ⊢ ρ x ≤ˣ ρ′ x′ ⦂ A≤

_→ˢ_∋_≤_ : ∀ {Γ Γ′ Δ Δ′} (Γ≤ : Γ ≤ᴳ Γ′) (Δ≤ : Δ ≤ᴳ Δ′) → (Γ →ˢ Δ) → (Γ′ →ˢ Δ′) → Set
Γ≤ →ˢ Δ≤ ∋ σ ≤ σ′ = ∀ {A A′} {A≤ : A ≤ A′} {E E′} {E≤ : E ≤ᵉ E′} {x x′}
  → Γ≤ ⊢ x ≤ˣ x′ ⦂ A≤
    -----------------------
  → Δ≤ ⊢ σ x ≤ᴹ σ′ x′ ⦂ ⟨ E≤ ⟩ A≤

_→ᵀ_∋_≤_ : ∀ {Γ Γ′ Δ Δ′} (Γ≤ : Γ ≤ᴳ Γ′) (Δ≤ : Δ ≤ᴳ Δ′) → (Γ →ᵀ Δ) → (Γ′ →ᵀ Δ′) → Set
Γ≤ →ᵀ Δ≤ ∋ s ≤ s′ = ∀ {A A′} {A≤ : A ≤ A′} {E E′} {E≤ : E ≤ᵉ E′} {M M′}
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ A≤
    -----------------------
  → Δ≤ ⊢ s M ≤ᴹ s′ M′ ⦂ ⟨ E≤ ⟩ A≤
```

Extension
```
ren⹁≤ : ∀ {Γ Γ′ Δ Δ′} {Γ≤ : Γ ≤ᴳ Γ′} {Δ≤ : Δ ≤ᴳ Δ′} {ρ : Γ →ᴿ Δ} {ρ′ : Γ′ →ᴿ Δ′}
  → Γ≤ →ᴿ Δ≤ ∋ ρ ≤ ρ′
    ------------------------------------------------------
  → ∀ {A A′} {A≤ : A ≤ A′} → Γ≤ ⹁ A≤ →ᴿ Δ≤ ⹁ A≤ ∋ ren⹁ ρ ≤ ren⹁ ρ′
ren⹁≤ ρ≤ Z≤Z       =  Z≤Z
ren⹁≤ ρ≤ (S≤S x≤)  =  S≤S (ρ≤ x≤)
```

```
ren∘ƛ-wrap : ∀ {Γ Δ A A′ P P′ E} {∓s : A′ => A} {±t : P =>ᶜ P′}
    (ρ : Γ →ᴿ Δ) (M : ∀ {E} → Γ ⊢ ⟨ E ⟩ (A ⇒ P))
  → ren ρ (ƛ-wrap ∓s ±t M {E = E}) ≡ ƛ-wrap ∓s ±t (ren ρ M)
ren∘ƛ-wrap {A′ = A′} {P = ⟨ E ⟩ _} {∓s = ∓s} {±t} ρ M
  rewrite (lift∘ren {A = A′} ρ (M {E = E})) = refl

sub∘ƛ-wrap : ∀ {Γ Δ A A′ P P′ E} {∓s : A′ => A} {±t : P =>ᶜ P′}
    (σ : Γ →ˢ Δ) (M : ∀ {E} → Γ ⊢ ⟨ E ⟩ (A ⇒ P))
  → sub σ (ƛ-wrap ∓s ±t M {E = E}) ≡ ƛ-wrap ∓s ±t (sub σ M)
sub∘ƛ-wrap {A′ = A′} {P = ⟨ E ⟩ _} {∓s = ∓s} {±t} σ M
  rewrite (lift∘sub {A = A′} σ (M {E = E})) = refl
```

Preservation of precision under renaming
```
ren≤ʰ : ∀ {Γ Γ′ Δ Δ′} {Γ≤ : Γ ≤ᴳ Γ′} {Δ≤ : Δ ≤ᴳ Δ′} {ρ : Γ →ᴿ Δ} {ρ′ : Γ′ →ᴿ Δ′} 
  → Γ≤ →ᴿ Δ≤ ∋ ρ ≤ ρ′
    -------------------------------------------
  → (∀ {P P′ Q Q′} {P≤ : P ≤ᶜ P′} {Q≤ : Q ≤ᶜ Q′} {H H′}
      → Γ≤ ⊢ H ≤ H′ ⦂ P≤ ➡ Q≤
      → Δ≤ ⊢ renʰ ρ H ≤ renʰ ρ′ H′ ⦂ P≤ ➡ Q≤)

ren≤ : ∀ {Γ Γ′ Δ Δ′} {Γ≤ : Γ ≤ᴳ Γ′} {Δ≤ : Δ ≤ᴳ Δ′} {ρ : Γ →ᴿ Δ} {ρ′ : Γ′ →ᴿ Δ′} 
  →  Γ≤ →ᴿ Δ≤ ∋ ρ ≤ ρ′
    -------------------------------------------
  → (∀ {A A′} {A≤ : A ≤ A′} {E E′} {E≤ : E ≤ᵉ E′} {M M′}
      → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ A≤
      → Δ≤ ⊢ ren ρ M ≤ᴹ ren ρ′ M′ ⦂ ⟨ E≤ ⟩ A≤)
ren≤ ρ≤ (`≤` x)              =  `≤` (ρ≤ x)
ren≤ ρ≤ (ƛ≤ƛ N≤)             =  ƛ≤ƛ (ren≤ (ren⹁≤ ρ≤) N≤)
ren≤ ρ≤ (·≤· L≤ M≤)          =  ·≤· (ren≤ ρ≤ L≤) (ren≤ ρ≤ M≤)
ren≤ ρ≤ ($≤$ k)              =  $≤$ k
ren≤ ρ≤ (⦅⦆≤⦅⦆ _⊕_ M≤ N≤)     =  ⦅⦆≤⦅⦆ _⊕_ (ren≤ ρ≤ M≤) (ren≤ ρ≤ N≤) 
ren≤ ρ≤ (⇑≤⇑ g M≤)           =  ⇑≤⇑ g (ren≤ ρ≤ M≤)
ren≤ ρ≤ (≤⇑ g M≤)            =  ≤⇑ g (ren≤ ρ≤ M≤)
ren≤ ρ≤ (▷≤ e M≤)           =  ▷≤ e (ren≤ ρ≤ M≤)
ren≤ ρ≤ (≤▷ e M≤)           =  ≤▷ e (ren≤ ρ≤ M≤)
ren≤ ρ≤ blame≤               =  blame≤
ren≤ {ρ = ρ} ρ≤ {A≤ = A≤} {E = E}
  (wrap≤ {N = N} {∓s = ∓s} {±t} i e ƛN≤ƛN′)
  rewrite ren∘ƛ-wrap {E = E} {∓s = ∓s} {±t = ±t} ρ (ƛ N)
  = wrap≤ i e (ren≤ ρ≤ ƛN≤ƛN′)
ren≤ {ρ′ = ρ′} ρ≤ {A≤ = A≤} {E′ = E′}
  (≤wrap {N′ = N′} {∓s = ∓s} {±t} i e ƛN≤ƛN′)
  rewrite ren∘ƛ-wrap {E = E′} {∓s = ∓s} {±t = ±t} ρ′ (ƛ N′)
  = ≤wrap i e (ren≤ ρ≤ ƛN≤ƛN′)
ren≤ ρ≤ (⟨⟩≤ M≤) = ⟨⟩≤ (ren≤ ρ≤ M≤)
ren≤ ρ≤ (≤⟨⟩ M≤) = ≤⟨⟩ (ren≤ ρ≤ M≤)
ren≤ ρ≤ (perform≤perform M≤) = perform≤perform (ren≤ ρ≤ M≤)
ren≤ ρ≤ (handle≤handle H≤ M≤) = handle≤handle (ren≤ʰ ρ≤ H≤) (ren≤ ρ≤ M≤)

ren≤ʰ ρ≤ H≤ = record
  { on-return = ren≤ (ren⹁≤ ρ≤) (on-return H≤)
  ; on-perform = ren≤-on-perform (on-perform H≤) }
  where
    open _⊢_≤_⦂_➡_

    ren≤-on-perform : ∀ {Eh Eh′ Ms Ms′}
      → On-Perform _ _ {Eh} {Eh′} Ms Ms′
      → On-Perform _ _ (ren-on-perform _ Ms) (ren-on-perform _ Ms′)
    ren≤-on-perform [] = []
    ren≤-on-perform ((refl , B⇒Q≤ , dom≡ , cod≡ , M≤) ∷ Ms≤)
      = (refl , B⇒Q≤ , dom≡ , cod≡ , ren≤ (ren⹁≤ (ren⹁≤ ρ≤)) M≤) ∷ ren≤-on-perform Ms≤
```

```
lift≤ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᴳ Γ′} {B B′} {B≤ : B ≤ B′}
          {A A′} {A≤ : A ≤ A′} {E E′} {E≤ : E ≤ᵉ E′} {M M′}
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ A≤
    ---------------------------------------
  → Γ≤ ⹁ B≤ ⊢ lift M ≤ᴹ lift M′ ⦂ ⟨ E≤ ⟩ A≤
lift≤ = ren≤ S≤S

lift≤ʰ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᴳ Γ′} {A A′} {A≤ : A ≤ A′}
          {P P′ Q Q′} {P≤ : P ≤ᶜ P′} {Q≤ : Q ≤ᶜ Q′} {H H′}
  → Γ≤ ⊢ H ≤ H′ ⦂ P≤ ➡ Q≤
    --------------------------------------
  → Γ≤ ⹁ A≤ ⊢ liftʰ H ≤ liftʰ H′ ⦂ P≤ ➡ Q≤
lift≤ʰ = ren≤ʰ S≤S 
```

## Substitution {#substitution-prec}

Extension
```
sub⹁≤ : ∀ {Γ Γ′ Δ Δ′} {Γ≤ : Γ ≤ᴳ Γ′} {Δ≤ : Δ ≤ᴳ Δ′} {σ : Γ →ˢ Δ} {σ′ : Γ′ →ˢ Δ′}
  → Γ≤ →ˢ Δ≤ ∋ σ ≤ σ′
    ------------------------------------------------------
  → ∀ {A A′} {A≤ : A ≤ A′} → Γ≤ ⹁ A≤ →ˢ Δ≤ ⹁ A≤ ∋ sub⹁ σ ≤ sub⹁ σ′
sub⹁≤ σ≤ Z≤Z       =  `≤` Z≤Z
sub⹁≤ σ≤ (S≤S x≤)  =  ren≤ S≤S (σ≤ x≤)
```

Preservation of precision under substitution
```
sub≤ : ∀ {Γ Γ′ Δ Δ′} {Γ≤ : Γ ≤ᴳ Γ′} {Δ≤ : Δ ≤ᴳ Δ′} {σ : Γ →ˢ Δ} {σ′ : Γ′ →ˢ Δ′}
  → Γ≤ →ˢ Δ≤ ∋ σ ≤ σ′
    -------------------------
  → Γ≤ →ᵀ Δ≤ ∋ sub σ ≤ sub σ′
sub≤ σ≤ (`≤` x)              =  σ≤ x
sub≤ σ≤ (ƛ≤ƛ N≤)             =  ƛ≤ƛ (sub≤ (sub⹁≤ σ≤) N≤)
sub≤ σ≤ (·≤· L≤ M≤)          =  ·≤· (sub≤ σ≤ L≤) (sub≤ σ≤ M≤)
sub≤ σ≤ ($≤$ k)              =  $≤$ k
sub≤ σ≤ (⦅⦆≤⦅⦆ _⊕_ M≤ N≤)     =  ⦅⦆≤⦅⦆ _⊕_ (sub≤ σ≤ M≤) (sub≤ σ≤ N≤)
sub≤ σ≤ (⇑≤⇑ g M≤)           =  ⇑≤⇑ g (sub≤ σ≤ M≤)
sub≤ σ≤ (≤⇑ g M≤)            =  ≤⇑ g (sub≤ σ≤ M≤)
sub≤ σ≤ (▷≤ e M≤)           =  ▷≤ e (sub≤ σ≤ M≤)
sub≤ σ≤ (≤▷ e M≤)           =  ≤▷ e (sub≤ σ≤ M≤)
sub≤ σ≤ blame≤               =  blame≤
sub≤ {σ = σ} σ≤ {E = E} (wrap≤ {N = N} {∓s = ∓s} {±t} i e ƛN≤ƛN′)
  rewrite sub∘ƛ-wrap {E = E} {∓s = ∓s} {±t} σ (ƛ N)
  =  wrap≤ i e (sub≤ σ≤ ƛN≤ƛN′)
sub≤ {σ′ = σ′} σ≤ {E′ = E′} (≤wrap {N′ = N′} {∓s = ∓s} {±t} i e ƛN≤ƛN′)
  rewrite sub∘ƛ-wrap {E = E′} {∓s = ∓s} {±t} σ′ (ƛ N′)
  =  ≤wrap i e (sub≤ σ≤ ƛN≤ƛN′)
sub≤ σ≤ (⟨⟩≤ M≤) = ⟨⟩≤ (sub≤ σ≤ M≤)
sub≤ σ≤ (≤⟨⟩ M≤) = ≤⟨⟩ (sub≤ σ≤ M≤)
sub≤ σ≤ (perform≤perform M≤) = perform≤perform (sub≤ σ≤ M≤)
sub≤ σ≤ (handle≤handle H≤ M≤) = handle≤handle sub≤ʰ (sub≤ σ≤ M≤)
  where
    open _⊢_≤_⦂_➡_

    sub≤-on-perform : ∀ {Eh Eh′ Ms Ms′}
      → On-Perform _ _ {Eh} {Eh′} Ms Ms′
      → On-Perform _ _ (sub-on-perform _ Ms) (sub-on-perform _ Ms′)
    sub≤-on-perform [] = []
    sub≤-on-perform ((refl , B⇒Q≤ , dom≡ , cod≡ , M≤) ∷ Ms≤)
      = (refl , B⇒Q≤ , dom≡ , cod≡ , sub≤ (sub⹁≤ (sub⹁≤ σ≤)) M≤) ∷ sub≤-on-perform Ms≤

    sub≤ʰ = record
      { on-return = sub≤ (sub⹁≤ σ≤) (on-return H≤)
      ; on-perform = sub≤-on-perform (on-perform H≤) }
```

Preservation of precision under substitution, special case for beta

```
σ₀≤σ₀ : ∀ {Γ Γ′ A A′} {M : ∀ {E} → Γ ⊢ ⟨ E ⟩ A} {M′ : ∀ {E′} → Γ′ ⊢ ⟨ E′ ⟩ A′} {Γ≤ : Γ ≤ᴳ Γ′} {s : A ≤ A′}
  → (∀ {E E′} {E≤ : E ≤ᵉ E′} → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ s)
  → Γ≤ ⹁ s →ˢ Γ≤ ∋ σ₀ M ≤ σ₀ M′
σ₀≤σ₀ M≤M′ Z≤Z         =  M≤M′
σ₀≤σ₀ M≤M′ (S≤S x≤x′)  =  `≤` x≤x′

[]≤[] : ∀ {Γ Γ′ A A′ B B′ E E′ N N′} {M : ∀ {E} → Γ ⊢ ⟨ E ⟩ A} {M′ : ∀ {E′} → Γ′ ⊢ ⟨ E′ ⟩ A′} {Γ≤ : Γ ≤ᴳ Γ′} {s : A ≤ A′} {t : B ≤ B′} {E≤ : E ≤ᵉ E′}
        → Γ≤ ⹁ s ⊢ N ≤ᴹ N′ ⦂ ⟨ E≤ ⟩ t
        → (∀ {E E′} {E≤ : E ≤ᵉ E′} → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ s)
          -----------------------------
        → Γ≤ ⊢ N [ M ] ≤ᴹ N′ [ M′ ] ⦂ ⟨ E≤ ⟩ t
[]≤[] N≤N′ M≤M′ =  sub≤ (σ₀≤σ₀ M≤M′) N≤N′
```

## Relating a term to its type erasure

```
ƛ≤ƛ★ : ∀ {Γ Γ′ A B E F F′ N N′} {Γ≤ : Γ ≤ᴳ Γ′} {F≤ : F ≤ᵉ F′} {p : A ⇒ ⟨ E ⟩ B ≤ ★ ⇒ ⟨ ☆ ⟩ ★}
  → Γ≤ ⹁ dom p ⊢ N ≤ᴹ N′ ⦂ cod p
    ----------------------------
  → Γ≤ ⊢ ƛ N ≤ᴹ ƛ★ N′ ⦂ ⟨ F≤ ⟩ (p ⇑ ★⇒★)
ƛ≤ƛ★ N≤N′ = ≤▷ refl (ƛ≤ƛ N≤N′)

·≤·★ : ∀ {Γ Γ′ A B E L L′ M M′} {Γ≤ : Γ ≤ᴳ Γ′} {p : A ⇒ ⟨ E ⟩ B ≤ ★ ⇒ ⟨ ☆ ⟩ ★}
    (let ⟨ E≤ ⟩ _ = cod p)
  → Γ≤ ⊢ L ≤ᴹ L′ ⦂ ⟨ E≤ ⟩ (p ⇑ ★⇒★)
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ dom p
    ------------------------------
  → Γ≤ ⊢ L · M ≤ᴹ L′ ·★ M′ ⦂ cod p
·≤·★ L≤L′ M≤M′ = ·≤· (≤▷ refl L≤L′) M≤M′

$≤$★ : ∀ {Γ Γ′ E ι} {Γ≤ : Γ ≤ᴳ Γ′} {E≤ : E ≤ᵉ ☆} (k : rep ι) → Γ≤ ⊢ $ k ≤ᴹ $★ k ⦂ ⟨ E≤ ⟩ (ι ≤★)
$≤$★ {ι = ι} k  =  ≤⇑ ($ ι) ($≤$ k)

⦅⦆≤⦅⦆★ : ∀ {Γ Γ′ E ι ι′ ι″ M M′ N N′} {Γ≤ : Γ ≤ᴳ Γ′} {E≤ : E ≤ᵉ ☆}
  → (_⊕_ : rep ι → rep ι′ → rep ι″)
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ (ι ≤★)
  → Γ≤ ⊢ N ≤ᴹ N′ ⦂ ⟨ E≤ ⟩ (ι′ ≤★)
    ------------------------------------------
  → Γ≤ ⊢ M ⦅ _⊕_ ⦆ N ≤ᴹ M′ ⦅ _⊕_ ⦆★ N′ ⦂ ⟨ E≤ ⟩ (ι″ ≤★)
⦅⦆≤⦅⦆★ _⊕_ M≤M′ N≤N′ = ≤▷ refl (⦅⦆≤⦅⦆ _⊕_ (≤▷ refl M≤M′) (≤▷ refl N≤N′))

⌈_⌉≤ᴳ : ∀ (Γ : Context) → Γ ≤ᴳ ⌈ Γ ⌉ᴳ
⌈ ∅ ⌉≤ᴳ          =  ∅
⌈ Γ ⹁ A ⌉≤ᴳ      =  ⌈ Γ ⌉≤ᴳ ⹁ A≤★

⌈_⌉≤ˣ : ∀ {Γ A} → (x : Γ ∋ A) → ⌈ Γ ⌉≤ᴳ ⊢ x ≤ˣ ⌈ x ⌉ˣ ⦂ A≤★
⌈ Z ⌉≤ˣ          =  Z≤Z
⌈ S x ⌉≤ˣ        =  S≤S ⌈ x ⌉≤ˣ

⌈_⌉≤ : ∀ {Γ E A} {M : Γ ⊢ ⟨ E ⟩ A} → (m : Static M) → ⌈ Γ ⌉≤ᴳ ⊢ M ≤ᴹ ⌈ m ⌉ ⦂ ⟨ E≤☆ ⟩ A≤★
⌈ ` x ⌉≤         =  `≤` ⌈ x ⌉≤ˣ
⌈ ƛ N ⌉≤         =  ƛ≤ƛ★ ⌈ N ⌉≤
⌈ L · M ⌉≤       =  ·≤·★ ⌈ L ⌉≤ ⌈ M ⌉≤
⌈ $ k ⌉≤         =  $≤$★ k
⌈ M ⦅ _⊕_ ⦆ N ⌉≤  =  ⦅⦆≤⦅⦆★ _⊕_ ⌈ M ⌉≤ ⌈ N ⌉≤
```

## Example {#example-prec}

```
inc≤inc★ : ∅ ⊢ inc ≤ᴹ inc★ ⦂ ⟨ ε≤☆ ⟩ ℕ⇒ℕ≤★
inc≤inc★ = ⌈ Inc ⌉≤

inc≤inc★′ : ∅ ⊢ inc ≤ᴹ inc★′ ⦂ ⟨ ε≤☆ ⟩ ℕ⇒ℕ≤★
inc≤inc★′ = ≤▷ refl (≤⟨⟩ (reflᴹ inc))

inc2≤inc★2★ : ∅ ⊢ inc · ($ 2) ≤ᴹ inc★ ·★ ($★ 2) ⦂ ⟨ ε≤☆ ⟩ ℕ≤★
inc2≤inc★2★ = ⌈ Inc · ($ 2) ⌉≤

inc2≤inc★′2★ : ∅ ⊢ inc · ($ 2) ≤ᴹ inc★′ ·★ ($★ 2) ⦂ ⟨ ε≤☆ ⟩ ℕ≤★
inc2≤inc★′2★ = ·≤·★ inc≤inc★′ ($≤$★ 2)
```

## Precision on frames

```
infix 3 _⊢_⇒ᶠ_∋_≤_

data _⊢_⇒ᶠ_∋_≤_ {Γ Γ′} (Γ≤ : Γ ≤ᴳ Γ′)
                {P P′} (P≤ : P ≤ᶜ P′)
            : ∀ {Q Q′} (Q≤ : Q ≤ᶜ Q′)
            →            Frame Γ P Q
            →            Frame Γ′ P′ Q′
            → Set where
  □ : Γ≤ ⊢ P≤ ⇒ᶠ P≤ ∋ □ ≤ □

  [_]·_ : ∀ {𝐸 𝐸′} {M M′} {A⇒B≤ : A ⇒ ⟨ E ⟩ B ≤ A′ ⇒ ⟨ E′ ⟩ B′}
      (let E≤ = _≤ᶜ_.effects (cod A⇒B≤))
    → (𝐸≤ : Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ A⇒B≤ ∋ 𝐸 ≤ 𝐸′)
    → (M≤ : Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ dom A⇒B≤)
      ----------------------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ cod A⇒B≤ ∋ [ 𝐸 ]· M ≤ [ 𝐸′ ]· M′

  _·[_] : ∀ {V V′} {𝐸 𝐸′} {A⇒B≤ : A ⇒ ⟨ E ⟩ B ≤ A′ ⇒ ⟨ E′ ⟩ B′}
      (let E≤ = _≤ᶜ_.effects (cod A⇒B≤))
    → ((v , v′ , _) : Value V × Value V′ × (Γ≤ ⊢ V ≤ᴹ V′ ⦂ ⟨ E≤ ⟩ A⇒B≤))
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ dom A⇒B≤ ∋ 𝐸 ≤ 𝐸′
      ----------------------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ cod A⇒B≤ ∋ v ·[ 𝐸 ] ≤ v′ ·[ 𝐸′ ]

  [_]⦅_⦆_ : ∀ {ι ι′ ι″} {𝐸 𝐸′} {M M′}
    → (𝐸≤ : Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id ∋ 𝐸 ≤ 𝐸′)
    → (f : rep ι → rep ι′ → rep ι″)
    → (M≤ : Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ id)
      ------------------------------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id ∋ [ 𝐸 ]⦅ f ⦆ M ≤ [ 𝐸′ ]⦅ f ⦆ M′

  _⦅_⦆[_] : ∀ {ι ι′ ι″} {V V′} {𝐸 𝐸′}
    → ((v , v′ , _) : Value V × Value V′ × (Γ≤ ⊢ V ≤ᴹ V′ ⦂ ⟨ E≤ ⟩ id))
    → (f : rep ι → rep ι′ → rep ι″)
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id ∋ 𝐸 ≤ 𝐸′
      ------------------------------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id ∋ v ⦅ f ⦆[ 𝐸 ] ≤ v′ ⦅ f ⦆[ 𝐸′ ]

  [_]⇑_ : ∀ {G 𝐸 𝐸′}
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id ∋ 𝐸 ≤ 𝐸′
    → (g : Ground G)
      --------------------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id ∋ [ 𝐸 ]⇑ g ≤ [ 𝐸′ ]⇑ g

  ≤⇑ : ∀ {G} {A≤G : A′ ≤ G} {g : Ground G} {𝐸 𝐸′}
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ A≤G ∋ 𝐸 ≤ 𝐸′
      --------------------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ (A≤G ⇑ g) ∋ 𝐸 ≤ [ 𝐸′ ]⇑ g

  ▷≤ : ∀ {A=>B : A => B} {B≤C : B ≤ C} {A≤C : A ≤ C} {𝐸 𝐸′}
    → commute≤ A=>B B≤C A≤C
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ A≤C ∋ 𝐸 ≤ 𝐸′
      --------------------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ B≤C ∋ [ 𝐸 ]▷ A=>B ≤ 𝐸′

  ≤▷ : ∀ {A≤B : A ≤ B} {B=>C : B => C} {A≤C : A ≤ C} {𝐸 𝐸′}
    → ≤commute A≤B B=>C A≤C
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ A≤B ∋ 𝐸 ≤ 𝐸′
      --------------------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ A≤C ∋ 𝐸 ≤ [ 𝐸′ ]▷ B=>C

  ⟨⟩≤ : ∀ {E=>F : E =>ᵉ F} {F≤E′ : F ≤ᵉ E′} {E≤E′ : E ≤ᵉ E′} {𝐸 𝐸′}
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤E′ ⟩ A≤ ∋ 𝐸 ≤ 𝐸′
      --------------------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ F≤E′ ⟩ A≤ ∋ [ 𝐸 ]▷⟨ E=>F ⟩ ≤ 𝐸′

  ≤⟨⟩ : ∀ {E≤F′ : E ≤ᵉ F′} {F′=>E′ : F′ =>ᵉ E′} {E≤E′ : E ≤ᵉ E′} {𝐸 𝐸′}
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤F′ ⟩ A≤ ∋ 𝐸 ≤ 𝐸′
      --------------------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤E′ ⟩ A≤ ∋ 𝐸 ≤ [ 𝐸′ ]▷⟨ F′=>E′ ⟩

  ″perform_[_]_ : ∀ {e} {𝐸 𝐸′}
    → ((e∈E , e∈E′) : e ∈☆ E × e ∈☆ E′)
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id ∋ 𝐸 ≤ 𝐸′
    → ∀ {A}
    → (eq : response e ≡ A)
      --------------------------------------------------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id ∋ (″perform e∈E [ 𝐸 ] eq) ≤ (″perform e∈E′ [ 𝐸′ ] eq)

  ′handle_[_] : ∀ {Q₁ Q₁′ Q₂ Q₂′} {Q₁≤ : Q₁ ≤ᶜ Q₁′} {Q₂≤ : Q₂ ≤ᶜ Q₂′} {H H′} {𝐸 𝐸′}
    → Γ≤ ⊢ H ≤ H′ ⦂ Q₁≤ ➡ Q₂≤
    → Γ≤ ⊢ P≤ ⇒ᶠ Q₁≤ ∋ 𝐸 ≤ 𝐸′
      ----------------------------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ Q₂≤ ∋ ′handle H [ 𝐸 ] ≤ ′handle H′ [ 𝐸′ ]

ren≤ᶠ : ∀ {ρ : Γ →ᴿ Δ} {ρ′ : Γ′ →ᴿ Δ′} {𝐸 𝐸′}
  → Γ≤ →ᴿ Δ≤ ∋ ρ ≤ ρ′
  → Γ≤ ⊢ P≤ ⇒ᶠ Q≤ ∋ 𝐸 ≤ 𝐸′
  → Δ≤ ⊢ P≤ ⇒ᶠ Q≤ ∋ renᶠ ρ 𝐸 ≤ renᶠ ρ′ 𝐸′
ren≤ᶠ ρ≤ □ = □
ren≤ᶠ ρ≤ ([ 𝐸≤ ]· M≤) = [ ren≤ᶠ ρ≤ 𝐸≤ ]· ren≤ ρ≤ M≤
ren≤ᶠ ρ≤ ((v , v′ , V≤) ·[ 𝐸≤ ]) = (ren-val _ v , ren-val _ v′ , ren≤ ρ≤ V≤) ·[ ren≤ᶠ ρ≤ 𝐸≤ ]
ren≤ᶠ ρ≤ ([ 𝐸≤ ]⦅ f ⦆ M≤) = [ ren≤ᶠ ρ≤ 𝐸≤ ]⦅ f ⦆ ren≤ ρ≤ M≤
ren≤ᶠ ρ≤ ((v , v′ , V≤) ⦅ f ⦆[ 𝐸≤ ]) = (ren-val _ v , ren-val _ v′ , ren≤ ρ≤ V≤) ⦅ f ⦆[ ren≤ᶠ ρ≤ 𝐸≤ ]
ren≤ᶠ ρ≤ ([ 𝐸≤ ]⇑ g) = [ ren≤ᶠ ρ≤ 𝐸≤ ]⇑ g
ren≤ᶠ ρ≤ (≤⇑ 𝐸≤) = ≤⇑ (ren≤ᶠ ρ≤ 𝐸≤)
ren≤ᶠ ρ≤ (▷≤ comm 𝐸≤) = ▷≤ comm (ren≤ᶠ ρ≤ 𝐸≤)
ren≤ᶠ ρ≤ (≤▷ comm 𝐸≤) = ≤▷ comm (ren≤ᶠ ρ≤ 𝐸≤)
ren≤ᶠ ρ≤ (⟨⟩≤ 𝐸≤) = ⟨⟩≤ (ren≤ᶠ ρ≤ 𝐸≤)
ren≤ᶠ ρ≤ (≤⟨⟩ 𝐸≤) = ≤⟨⟩ (ren≤ᶠ ρ≤ 𝐸≤)
ren≤ᶠ ρ≤ (″perform (e∈E , e∈E′) [ 𝐸≤ ] eq) = ″perform (e∈E , e∈E′) [ ren≤ᶠ ρ≤ 𝐸≤ ] eq
ren≤ᶠ ρ≤ (′handle H≤ [ 𝐸≤ ]) = ′handle (ren≤ʰ ρ≤ H≤) [ ren≤ᶠ ρ≤ 𝐸≤ ]

lift≤ᶠ : ∀ {𝐸 𝐸′}
  → Γ≤ ⊢ P≤ ⇒ᶠ Q≤ ∋ 𝐸 ≤ 𝐸′
  → Γ≤ ⹁ A≤ ⊢ P≤ ⇒ᶠ Q≤ ∋ liftᶠ 𝐸 ≤ liftᶠ 𝐸′
lift≤ᶠ = ren≤ᶠ S≤S

⟦⟧≤⟦⟧ : ∀ {𝐸 𝐸′ M M′}
  → Γ≤ ⊢ P≤ ⇒ᶠ Q≤ ∋ 𝐸 ≤ 𝐸′
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ P≤
  → Γ≤ ⊢ 𝐸 ⟦ M ⟧ ≤ᴹ 𝐸′ ⟦ M′ ⟧ ⦂ Q≤
⟦⟧≤⟦⟧ □ M≤ = M≤
⟦⟧≤⟦⟧ ([ 𝐸≤ ]· N≤) M≤ = ·≤· (⟦⟧≤⟦⟧ 𝐸≤ M≤) N≤
⟦⟧≤⟦⟧ ((v , v′ , V≤) ·[ 𝐸≤ ]) M≤ = ·≤· V≤ (⟦⟧≤⟦⟧ 𝐸≤ M≤)
⟦⟧≤⟦⟧ ([ 𝐸≤ ]⦅ f ⦆ N≤) M≤ = ⦅⦆≤⦅⦆ f (⟦⟧≤⟦⟧ 𝐸≤ M≤) N≤
⟦⟧≤⟦⟧ ((v , v′ , V≤) ⦅ f ⦆[ 𝐸≤ ]) M≤ = ⦅⦆≤⦅⦆ f V≤ (⟦⟧≤⟦⟧ 𝐸≤ M≤)
⟦⟧≤⟦⟧ ([ 𝐸≤ ]⇑ g) M≤ = ⇑≤⇑ g (⟦⟧≤⟦⟧ 𝐸≤ M≤)
⟦⟧≤⟦⟧ (≤⇑ 𝐸≤) M≤ = ≤⇑ _ (⟦⟧≤⟦⟧ 𝐸≤ M≤)
⟦⟧≤⟦⟧ (▷≤ comm 𝐸≤) M≤ = ▷≤ comm (⟦⟧≤⟦⟧ 𝐸≤ M≤)
⟦⟧≤⟦⟧ (≤▷ comm 𝐸≤) M≤ = ≤▷ comm (⟦⟧≤⟦⟧ 𝐸≤ M≤)
⟦⟧≤⟦⟧ (⟨⟩≤ 𝐸≤) M≤ = ⟨⟩≤ (⟦⟧≤⟦⟧ 𝐸≤ M≤)
⟦⟧≤⟦⟧ (≤⟨⟩ 𝐸≤) M≤ = ≤⟨⟩ (⟦⟧≤⟦⟧ 𝐸≤ M≤)
⟦⟧≤⟦⟧ (″perform (e∈E , e∈E′) [ 𝐸≤ ] eq) M≤ = perform≤perform (⟦⟧≤⟦⟧ 𝐸≤ M≤)
⟦⟧≤⟦⟧ (′handle H≤ [ 𝐸≤ ]) M≤ = handle≤handle H≤ (⟦⟧≤⟦⟧ 𝐸≤ M≤)
```
