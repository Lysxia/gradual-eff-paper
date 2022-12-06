{% extends "index.html.template" %}

```
{-# OPTIONS --guardedness #-}
module Code where

open import Utils

postulate todo : {A : Set} → A
```

```
module T where
  data Type : Set where
    ★ : Type
    _⇒_ : Type → Type → Type
    ′ℕ : Type

  private variable
    A A′ B B′ G H : Type

  module Fake where
```

{% block precision %}
```
    data _≤_ : Type → Type → Set where

      ≤★ :
          -----
          A ≤ ★

      id :
          -----
          A ≤ A

      _⇒_ :
          A ≤ A′
        → B ≤ B′
          -------------------
        → (A ⇒ B) ≤ (A′ ⇒ B′)
```
{% endblock %}

{% block ground %}
```
  data Ground : Type → Set where

    ★⇒★ : Ground (★ ⇒ ★)

    ′ℕ : Ground ′ℕ
```
{% endblock %}

{% block precisionbis %}
```
  data _≤_ : Type → Type → Set where
    _⇑_ :        -- replaces the rule ≤★ : A ≤ ★
        (p : A ≤ G)
      → (g : Ground G)
        -----
      → A ≤ ★

    id :
        -----
        A ≤ A

    _⇒_ :
        A ≤ A′
      → B ≤ B′
        -------------------
      → (A ⇒ B) ≤ (A′ ⇒ B′)
```
{% endblock %}

```
  data Context : Set where
    ∅ : Context
    _▷_ : Context → Type → Context
  data Term : Set where

  private variable
    Γ : Context
    M : Term
```

```
  module W where
```

{% block precisionsubsumption %}
```
    data _⊢_⦂_ : Context → Term → Type → Set where

      materialize :
           A ≤ B
        →  Γ ⊢ M ⦂ B
           ---------
        →  Γ ⊢ M ⦂ A

      -- etc.
```
{% endblock %}
{% block precisionsubsumption2 %}
```
  data _⊢_⦂_ : Context → Term → Type → Set where

    materialize :
         (p : A ≤ B)
      →  Γ ⊢ M ⦂ B
         ---------
      →  Γ ⊢ M ⦂ A

    -- etc.
```
{% endblock %}

```
  infix 4 +_ -_ _=>_
```

{% block castdef %}
```
  data _=>_ : Type → Type → Set where
    +_ :
         A ≤ B
         ------ upcast
      →  A => B

    -_ :
         B ≤ A
         ------ downcast
      →  A => B
```
{% endblock %}

```
  infix 4 _⊢_ _∋_
```

```
  data _∋_ : Context → Type → Set where
    Z : Γ ▷ A ∋ A
```

{% block castcalculus %}
```
  data _⊢_ : Context → Type → Set where

    _·_ :
         Γ ⊢ A ⇒ B
      →  Γ ⊢ A
         --------- application
      →  Γ ⊢ B

    ƛ_ :
         Γ ▷ A ⊢ B
         --------- abstraction
      →  Γ ⊢ A ⇒ B

    `_ :
         Γ ∋ A
         ----- variable
      →  Γ ⊢ A

    -- etc.
```
{% endblock %}

{% block castrule %}
```
    cast :
         A => B  -- New cast construct
      →  Γ ⊢ A
         ---------
      →  Γ ⊢ B
```
{% endblock %}


{% block boxrule %}
```
    _⇑_ :
         (M : Γ ⊢ G)
      →  (g : Ground G)
         -------------- box
      →  Γ ⊢ ★
```
{% endblock %}

```
    blame : Γ ⊢ A
```

```
  ℕ⇒ℕ≤★⇒★ : (★ ⇒ ★) => (′ℕ ⇒ ′ℕ)
  ℕ⇒ℕ≤★⇒★ = todo

  _ : _
  _ = λ Γ →
    let materialize = cast in
```

{% block exampletyping %}
{% block exampletyping2 %}
```
    λ (f : Γ ⊢ ★ ⇒ ★)
      (x : Γ ⊢ ′ℕ) →
      ------------------------------------
      (materialize ℕ⇒ℕ≤★⇒★ f) · x  -- : ′ℕ
```
{% endblock %}
{% endblock %}

```
  lift : Γ ⊢ A → Γ ▷ B ⊢ A
  lift = todo
```


```
  data Value : Γ ⊢ A → Set where

  infix 2 _↦_ _—→_
```

```
  data _==>_ : Type → Type → Set where
    _⇒_ : A′ => A → B => B′ → (A ⇒ B) ==> (A′ ⇒ B′)

  split : (A ⇒ B) => (A′ ⇒ B′) → (A ⇒ B) ==> (A′ ⇒ B′)
  split = todo
```

{% block opsem %}
```
  data _↦_ : Γ ⊢ A → Γ ⊢ A → Set where
```
{% endblock %}

{% block opsem1 %}
```
    expand : ∀ {V : Γ ⊢ A} {p : A ≤ G}
      → Value V
      → (g : Ground G)
        -------------------------------------
      → cast (+ (p ⇑ g)) V ↦ cast (+ p) V ⇑ g
```
{% endblock %}

{% block opsem2 %}
```
    collapse : ∀ {V : Γ ⊢ G} {p : A ≤ G}
      → Value V
      → (g : Ground G)
        ---------------------------------------
      → cast (- (p ⇑ g)) (V ⇑ g) ↦ cast (- p) V
```
{% endblock %}

{% block opsem3 %}
```
    collide  : ∀ {V : Γ ⊢ G} {p : A ≤ H}
      → Value V
      → (g : Ground G)
      → (h : Ground H)
      → G ≢ H
        --------------------------------
      → cast (- (p ⇑ h)) (V ⇑ g) ↦ blame
```
{% endblock %}

{% block wrap %}
```
    wrap : ∀ {N : Γ ▷ A ⊢ B}
        {∓s : A′ => A} {±t : B => B′} {±p : A ⇒ B => A′ ⇒ B′}
      → split ±p ≡ ∓s ⇒ ±t
        ----------------------------------------------------
      → cast ±p (ƛ N) ↦ ƛ (cast ±t (lift (ƛ N) · cast ∓s (` Z)))
```
{% endblock %}

```
  module _ (Γ : Context) where
```

```

    _ :  Γ ⊢ ′ℕ ⇒ ′ℕ
         -----------
      →  Type
    _ = λ f →
      let
```
{% block boxexample %}
```
          M = cast (+ ((id ⇑ ′ℕ) ⇒ (id ⇑ ′ℕ)) ⇑ ★⇒★) f
```
{% endblock %}

```
          M₂ = blame
```

{% block boxexample2 %}
```
            -- by expand
            ↦  cast (+ ((id ⇑ ′ℕ) ⇒ (id ⇑ ′ℕ))) f ⇑ ★⇒★
```
{% endblock %}

```
          M₃ = blame
```

{% block boxexample3 %}
```
            -- by wrap
            ↦  (ƛ cast (+ (id ⇑ ′ℕ))
                        ( lift f
                        · cast (- (id ⇑ ′ℕ)) (` Z)))  ⇑ ★⇒★
            --  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
            --  Value ((ƛ _) ⇑ ★⇒★)
```
{% endblock %}

```
      in ★
```

cast (∓s ⇒ ±t) (λ x. N x)  ↦  λ x. cast ±t (N (cast ∓s x))

```
module W where
  open import Type
  open import Core
  open import Progress as Prog hiding (Progress; step; done; blame; progress)
  private variable
    A : CType
```

{% block progress %}
```
  data Progress : (∅ ⊢ A) → Set where

    step : ∀ {M N : ∅ ⊢ A}
      →  M —→ N
         ----------
      →  Progress M

    done : ∀ {M : ∅ ⊢ A}
      →  Value M
         ----------
      →  Progress M

    blame : ∀ {Q}
      →  (E : Frame ∅ Q A)
         ---------------------
      →  Progress (E ⟦ blame ⟧)
```
{% endblock %}

{% block progress2 %}
```
  -- Theorem
  progress :
      (M : ∅ ⊢ A)
      -----------
    → Progress M
  progress = todo
```
{% endblock %}


{% block test %}
```
import Data.Nat.Base
open import Utils
open import Type
open import Core
open import Prec hiding (cast≤)

data _⊢¹_ (ℰ : Set) : Set where
```
{% endblock %}

```
private variable
  A B C : Type
  P P′ Q R : CType
  Γ Γ′ : Context
  Γ≤ : Γ ≤ᴳ Γ′
```

```
private variable
  M : Γ ⊢ P
  M′ : Γ′ ⊢ P′

module B where
```

{% block cast_left_plus %}
```
  cast⁺≤ : {p : P ≤ᶜ Q} {q : Q ≤ᶜ R} {r : P ≤ᶜ R}
    →  p ⨟ᶜ q ≡ r       -- ← commutative triangle
    →  Γ≤ ⊢ M ≤ᴹ M′ ⦂ r
       ---------------------------
    →  Γ≤ ⊢ cast (+ p) M ≤ᴹ M′ ⦂ q
```
{% endblock %}

```
  cast⁺≤ = todo
```

{% block cast_left_minus %}
```
  cast⁻≤ : {p : Q ≤ᶜ P} {q : Q ≤ᶜ R} {r : P ≤ᶜ R}
    →  p ⨟ᶜ r ≡ q       -- ← commutative triangle
    →  Γ≤ ⊢ M ≤ᴹ M′ ⦂ r
       --------------------------
    →  Γ≤ ⊢ cast (- p) M ≤ᴹ M′ ⦂ q
```
{% endblock %}

```
  cast⁻≤ = todo
```

```
module A where
```

{% block cast_left_plus_2 %}
```
  cast⁺≤ : {P≤Q : P ≤ᶜ Q} {Q≤R : Q ≤ᶜ R} {P≤R : P ≤ᶜ R}
    →  P≤Q ⨟ᶜ Q≤R ≡ P≤R       -- ← commutative triangle
    →  Γ≤ ⊢ M ≤ᴹ M′ ⦂ P≤R
       -------------------------------
    →  Γ≤ ⊢ cast (+ P≤Q) M ≤ᴹ M′ ⦂ Q≤R
```
{% endblock %}

```
  cast⁺≤ = todo
```

{% block cast_left_minus_2 %}
```
  cast⁻≤ : {Q≤P : Q ≤ᶜ P} {Q≤R : Q ≤ᶜ R} {P≤R : P ≤ᶜ R}
    →  Q≤P ⨟ᶜ P≤R ≡ Q≤R       -- ← commutative triangle
    →  Γ≤ ⊢ M ≤ᴹ M′ ⦂ P≤R
       -------------------------------
    →  Γ≤ ⊢ cast (- Q≤P) M ≤ᴹ M′ ⦂ Q≤R
```
{% endblock %}

```
  cast⁻≤ = todo
```
