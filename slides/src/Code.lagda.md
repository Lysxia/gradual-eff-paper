{% extends "index.html.template" %}

```
{-# OPTIONS --guardedness #-}
module Code where
```

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
  P P′ Q R : Typeᶜ
  Γ Γ′ : Context
  Γ≤ : Γ ≤ᴳ Γ′
  M : Γ ⊢ P
  M′ : Γ′ ⊢ P′

postulate todo : {A : Set} → A
```

```
module A where
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
module B where
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
