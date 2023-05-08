# Precision on terms

The gradual guarantee says that the behavior of a program doesn't
significantly change when we add or remove type annotations.
Formally, if a well-typed term `M` steps to `N`, then a term `M′` which is less precise
than `M` steps to a term `N′` which is less precise than `N′`.

In order to state this theorem in Agda, the first step is to define the
precision relation on contexts, terms, and frames.

\iffalse
```
module Prec where

open import Utils
open import Type
open import Core as Core hiding (On-Perform)
open import Progress
open import VecPointwise2
```

```
private variable
  Γ Γ′ Γ″ Δ Δ′ : Context
  P P′ P″ Q Q′ R R′ : CType
  A A′ A″ B B′ B″ C : Type
  E E′ E″ F F′ : Effect
  P≤ : P ≤ᶜ P′
  Q≤ : Q ≤ᶜ Q′
  A≤ : A ≤ A′
  B≤ : B ≤ B′
  E≤ : E ≤ᵉ E′
  F≤ : F ≤ᵉ F′
```

\fi

## Precision on contexts

Viewing contexts as lists of types, context precision is the
pointwise lifting of type precision.

\iffalse
```
infix 4 _≤ᴳ_
infixl 5 _▷_
```
\fi

```
data _≤ᴳ_ : Context → Context → Set where

  ∅ :
      ------
      ∅ ≤ᴳ ∅

  _▷_ :
      Γ ≤ᴳ Γ′
    → A ≤ A′
      ------------------
    → Γ ▷ A ≤ᴳ Γ′ ▷ A′
```

\iffalse
```
private variable
  Γ≤ : Γ ≤ᴳ Γ′
  Δ≤ : Δ ≤ᴳ Δ′
```
\fi

Context precision is reflexive.
```
idᴳ : Γ ≤ᴳ Γ
idᴳ {∅}      =  ∅
idᴳ {Γ ▷ A}  =  idᴳ ▷ id
```

Context precision is transitive.
```
_⨟ᴳ_ : Γ ≤ᴳ Γ′ → Γ′ ≤ᴳ Γ″ → Γ ≤ᴳ Γ″
∅ ⨟ᴳ ∅                    =  ∅
(Γ≤ ▷ A≤) ⨟ᴳ (Γ′≤ ▷ A′≤)  =  (Γ≤ ⨟ᴳ Γ′≤) ▷ (A≤ ⨟ A′≤)
```

From a proof-relevant perspective, context precision defines a category,
where `idᴳ` is the identity morphism, and `_⨟ᴳ_` is morphism composition.
They satisfy the following laws: \lyx{TODO: associativity?}
```
left-idᴳ : (Γ≤Δ : Γ ≤ᴳ Δ) → idᴳ ⨟ᴳ Γ≤Δ ≡ Γ≤Δ
left-idᴳ ∅ = refl
left-idᴳ (Γ≤Δ ▷ p) rewrite left-idᴳ Γ≤Δ
                         | left-id p = refl

right-idᴳ :(Γ≤Δ : Γ ≤ᴳ Δ) → Γ≤Δ ⨟ᴳ idᴳ ≡ Γ≤Δ
right-idᴳ ∅ = refl
right-idᴳ (Γ≤Δ ▷ p) rewrite right-idᴳ Γ≤Δ
                          | right-id p = refl
```

## Precision on variables

Variable precision `Γ≤ ⊢ x ≤ˣ x′ ⦂ A≤` relates variables `x` and `x′` that
structurally represent the same natural number, \ie{} the same index in
contexts of the same length.

Viewed in a proof-relevant manner, context precision is a type of heterogeneous
lists of type precision proofs, and variable precision is the corresponding type
of indices.
\lyx{Notation proposal: use `A≤` instead of `p`, `q`, `r` for precision proofs `A ≤ A′`}

\iffalse
```
infix 3 _⊢_≤ˣ_⦂_
```
\fi

```
data _⊢_≤ˣ_⦂_ : Γ ≤ᴳ Γ′
              → Γ ∋ A
              → Γ′ ∋ A′
              → A ≤ A′
              → Set where

  Z≤Z : {Γ≤ : Γ ≤ᴳ Γ′} {A≤ : A ≤ A′}
      ----------------------
    → Γ≤ ▷ A≤ ⊢ Z ≤ˣ Z ⦂ A≤

  S≤S : ∀ {x x′} {Γ≤ : Γ ≤ᴳ Γ′}
      {A≤ : A ≤ A′} {B≤ : B ≤ B′}
    → Γ≤ ⊢ x ≤ˣ x′ ⦂ A≤ 
      ---------------------------
    → Γ≤ ▷ B≤ ⊢ S x ≤ˣ S x′ ⦂ A≤
```

## Commuting diagram

When defining term precision, the key rules are those that relate casts.
If (1) `M : Γ ⊢ P` is more precise than `M′ : Γ′ ⊢ P′`,
(2) there is a cast `P =>ᶜ Q`, and (3) `Q` is more precise than `P′`,
then `cast ±p M : ⊢ Γ ⊢ Q` is more precise than `M′ : Γ′ ⊢ P′`.
(And similarly for a cast on the right.)

In addition, the cast `P =>ᶜ Q` and the precision relations
`P ≤ᶜ P′` and `Q ≤ᶜ Q′` should form a commutative triangle.
\lyx{explain motivation}

```
commute≤ᶜ : (±p : P =>ᶜ Q) (q : Q ≤ᶜ R)
            (r : P ≤ᶜ R) → Set
commute≤ᶜ (+ p) q r = p ⨟ᶜ q ≡ r
commute≤ᶜ (- p) q r = p ⨟ᶜ r ≡ q
```

A similar commutative triangle arises for casts on the right of term precision.
```
≤commuteᶜ : (p : P ≤ᶜ Q) (±q : Q =>ᶜ R)
            (r : P ≤ᶜ R) → Set
≤commuteᶜ p (+ q) r  =  p ⨟ᶜ q ≡ r
≤commuteᶜ p (- q) r  =  r ⨟ᶜ q ≡ p
```

The same commutative triangles can be defined on value type precision.
```
commute≤ : (±p : A => B) (q : B ≤ C)
           (r : A ≤ C) → Set
commute≤ (+ p) q r  =  p ⨟ q ≡ r
commute≤ (- p) q r  =  p ⨟ r ≡ q

≤commute : (p : A ≤ B) (±q : B => C)
           (r : A ≤ C) → Set
≤commute p (+ q) r  =  p ⨟ q ≡ r
≤commute p (- q) r  =  r ⨟ q ≡ p
```

\iffalse
We could also define it on effect types, but instead we make it a trivial
relation.
```
commute≤ᵉ : ∀ {E F G} (±p : E =>ᵉ F)
  (q : F ≤ᵉ G) (r : E ≤ᵉ G) → Set
commute≤ᵉ p q r  =  ⊤

≤commuteᵉ : ∀ {E Q G} (p : E ≤ᵉ Q)
  (±q : Q =>ᵉ G) (r : E ≤ᵉ G) → Set
≤commuteᵉ p q r  =  ⊤
```

Indeed, the structure of effect precision is simpler than type precision, so it
seems fair to consider them to be unique.\lyx{I'm not 100% certain of that}
```
unique-≤ᵉ : {E≤ E≤′ : E ≤ᵉ F} → E≤ ≡ E≤′
unique-≤ᵉ {E≤ = id} {E≤′ = id} = refl
unique-≤ᵉ {E≤ = ¡≤☆} {E≤′ = ¡≤☆} = refl
```

Thanks to that assumption on effect precision, there is an equivalence between
the commutative triangles on value type precision and those on computation type
precision, with `returns≤` and `≤returns` in one direction, and `pure≤` and
`≤pure` in the other.

```
returns≤ : ∀ {P Q R} {±p : P =>ᶜ Q}
    {q : Q ≤ᶜ R} {r : P ≤ᶜ R}
  → commute≤ᶜ ±p q r
  → commute≤ (=>ᶜ-returns ±p) (_≤ᶜ_.returns q) (_≤ᶜ_.returns r)
returns≤ {±p = + _} refl = refl
returns≤ {±p = - _} refl = refl

≤returns : ∀ {P Q R} {p : P ≤ᶜ Q}
    {±q : Q =>ᶜ R} {r : P ≤ᶜ R}
  → ≤commuteᶜ p ±q r
  → ≤commute (_≤ᶜ_.returns p) (=>ᶜ-returns ±q) (_≤ᶜ_.returns r)
≤returns {±q = + _} refl = refl
≤returns {±q = - _} refl = refl

pure≤ : ∀ {E F A B C} {E≤F : E ≤ᵉ F}
    {±p : A => B} {q : B ≤ C} {r : A ≤ C}
  → commute≤ ±p q r
  → commute≤ᶜ (pure± ±p) (⟨ E≤F ⟩ q) (⟨ E≤F ⟩ r)
pure≤ {±p = + _} refl = cong (⟨_⟩ _) unique-≤ᵉ
pure≤ {±p = - _} refl = cong (⟨_⟩ _) unique-≤ᵉ

≤pure : ∀ {E F A B C} {p : A ≤ B}
    {±q : B => C} {r : A ≤ C} {E≤F : E ≤ᵉ F}
  → ≤commute p ±q r
  → ≤commuteᶜ (⟨ E≤F ⟩ p) (pure± ±q) (⟨ E≤F ⟩ r)
≤pure {±q = + _} refl = refl
≤pure {±q = - _} refl = refl
```

An inversion lemma on commutative triangles where the two precision sides
consist of a box rule `_ ⇑ g`.
```
drop⇑ : ∀ {A B G} {±p : A => B}
    {q : B ≤ G} {r : A ≤ G} {g : Ground G}
  → commute≤ ±p (q ⇑ g) (r ⇑ g)
    ---------------------------
  → commute≤ ±p q r
drop⇑ {±p = + _} refl = refl
drop⇑ {±p = - _} refl = refl
```

Inversion lemmas when the cast side of a commutative triangle is an identity:
the commutative triangle contracts into an equation between the two remaining
sides.
```
ident≤ᶜ : ∀ {E F G A B} {q r : A ≤ B}
    {E≤G : E ≤ᵉ G} {F≤G : F ≤ᵉ G}
  → (±p : ⟨ E ⟩ A =>ᶜ ⟨ F ⟩ A)
  → splitᶜ ±p ≡ id
  → commute≤ᶜ ±p (⟨ F≤G ⟩ q) (⟨ E≤G ⟩ r)
    -----
  → q ≡ r
ident≤ᶜ {q = q} (+ ⟨ _ ⟩ id) refl refl
  rewrite left-id q = refl
ident≤ᶜ {r = r} (- ⟨ _ ⟩ id) refl refl
  rewrite left-id r = refl

≤identᶜ : ∀ {E F G A B} {p r : A ≤ B}
    {E≤F : E ≤ᵉ F} {E≤G : E ≤ᵉ G}
  → (±q : ⟨ F ⟩ B =>ᶜ ⟨ G ⟩ B)
  → splitᶜ ±q ≡ id
  → ≤commuteᶜ (⟨ E≤F ⟩ p) ±q (⟨ E≤G ⟩ r)
    -----
  → p ≡ r
≤identᶜ (+ ⟨ _ ⟩ id) refl refl = refl
≤identᶜ (- ⟨ _ ⟩ id) refl refl = refl

ident≤ : ∀ {A B} {q r : A ≤ B}
  → (±p : A => A)
  → split ±p ≡ id
  → commute≤ ±p q r
    -----
  → q ≡ r
ident≤ {q = q} (+ id) refl refl
  rewrite left-id q = refl
ident≤ {r = r} (- id) refl refl
  rewrite left-id r = refl

≤ident : ∀ {A B} {p r : A ≤ B}
  → (±q : B => B)
  → split ±q ≡ id
  → ≤commute p ±q r
    -----
  → p ≡ r
≤ident (+ id) refl refl = refl
≤ident (- id) refl refl = refl
```

Inversion lemmas when the cast side of a commutative triangle is a function
cast. It projects into commutative triangles relating respectively the domains
and codomains of the function types.
```
dom≤ :  ∀ {A A′ A″ E E′ E″ B B′ B″}
    {±p : A ⇒ ⟨ E ⟩ B => A′ ⇒ ⟨ E′ ⟩ B′}
    {q : A′ ⇒ ⟨ E′ ⟩ B′ ≤ A″ ⇒ ⟨ E″ ⟩ B″}
    {r : A ⇒ ⟨ E ⟩ B ≤ A″ ⇒ ⟨ E″ ⟩ B″}
    {∓s : A′ => A} {±t : B => B′} {±e : E =>ᵉ E′}
  → split ±p ≡ ∓s ⇒⟨ ±e ⟩ ±t
  → commute≤ ±p q r
    ---------------------------
  → commute≤ ∓s (dom r) (dom q)
dom≤ {±p = + s ⇒ t} {q = q} refl refl
  = dom-⨟ (s ⇒ t) q
dom≤ {±p = - s ⇒ t} {r = r} refl refl
  = dom-⨟ (s ⇒ t) r

cod≤ :  ∀ {A A′ A″ E E′ E″ B B′ B″}
    {±p : A ⇒ ⟨ E ⟩ B => A′ ⇒ ⟨ E′ ⟩ B′}
    {q : A′ ⇒ ⟨ E′ ⟩ B′ ≤ A″ ⇒ ⟨ E″ ⟩ B″}
    {r : A ⇒ ⟨ E ⟩ B ≤ A″ ⇒ ⟨ E″ ⟩ B″}
    {∓s : A′ => A} {±t : B => B′} {±e : E =>ᵉ E′}
  → split ±p ≡ ∓s ⇒⟨ ±e ⟩ ±t
  → commute≤ ±p q r
    ---------------------------
  → commute≤ ±t (cod q) (cod r)
cod≤ {±p = + s ⇒ t} {q = q} refl refl
  = cod-⨟ (s ⇒ t) q
cod≤ {±p = - s ⇒ t} {r = r} refl refl
  = cod-⨟ (s ⇒ t) r

≤dom :  ∀ {A A′ A″ E E′ E″ B B′ B″}
    {p : A ⇒ ⟨ E ⟩ B ≤ A′ ⇒ ⟨ E′ ⟩ B′}
    {±q : A′ ⇒ ⟨ E′ ⟩ B′ => A″ ⇒ ⟨ E″ ⟩ B″}
    {r : A ⇒ ⟨ E ⟩ B ≤ A″ ⇒ ⟨ E″ ⟩ B″}
    {∓s : A″ => A′} {±t : B′ => B″} {±e : E′ =>ᵉ E″}
  → split ±q ≡ ∓s ⇒⟨ ±e ⟩ ±t
  → ≤commute p ±q r
    ---------------------------
  → ≤commute (dom r) ∓s (dom p)
≤dom {p = p} {±q = + s ⇒ t} {r = r} refl refl
  = dom-⨟ p (s ⇒ t)
≤dom {p = p} {±q = - s ⇒ t} {r = r} refl refl
  = dom-⨟ r (s ⇒ t)

≤cod :  ∀ {A A′ A″ E E′ E″ B B′ B″}
    {p : A ⇒ ⟨ E ⟩ B ≤ A′ ⇒ ⟨ E′ ⟩ B′}
    {±q : A′ ⇒ ⟨ E′ ⟩ B′ => A″ ⇒ ⟨ E″ ⟩ B″}
    {r : A ⇒ ⟨ E ⟩ B ≤ A″ ⇒ ⟨ E″ ⟩ B″}
    {∓s : A″ => A′} {±t : B′ => B″} {±e : E′ =>ᵉ E″}
  → split ±q ≡ ∓s ⇒⟨ ±e ⟩ ±t
  → ≤commute p ±q r
    ---------------------------
  → ≤commute (cod p) ±t (cod r)
≤cod {p = p} {±q = + s ⇒ t} refl refl
  = cod-⨟ p (s ⇒ t)
≤cod {±q = - s ⇒ t} {r = r} refl refl
  = cod-⨟ r (s ⇒ t)
```
\fi

## Precision on terms

Term precision `_⊢_≤ᴹ_⦂_` and handler precision `_⊢_≤_⦂_⇒ʰ_` are defined mutually recursively.

\iffalse
```
infix 3 _⊢_≤ᴹ_⦂_ _⊢_≤_⦂_⇒ʰ_
```
\fi

```
data _⊢_≤ᴹ_⦂_ {Γ Γ′} (Γ≤ : Γ ≤ᴳ Γ′)
  : ∀ {A A′} → Γ ⊢ A → Γ′ ⊢ A′ → A ≤ᶜ A′ → Set
record _⊢_≤_⦂_⇒ʰ_ {Γ Γ′} (Γ≤ : Γ ≤ᴳ Γ′)
  {P P′ Q Q′}
  (H : Γ ⊢ P ⇒ʰ Q)
  (H′ : Γ′ ⊢ P′ ⇒ʰ Q′)
  (P≤ : P ≤ᶜ P′)
  (Q≤ : Q ≤ᶜ Q′) : Set
```

Start by defining term precision.
For constructs other than casts, the general rule is "a term `M` is more precise than `M′` if
the subterms of `M` are more precise than the subterms of of `M′`".
```
data _⊢_≤ᴹ_⦂_ {Γ Γ′} Γ≤ where
```

We defined variable precision `_⊢_≤ˣ_⦂_` previously.
Note that the effects on both sides may be arbitrary effects `E` and `E′` satisfying `E ≤ᵉ E′`.
```
  `≤` : ∀ {x x′} {pᵉ : E ≤ᵉ E′} {p : A ≤ A′}
    → Γ≤ ⊢ x ≤ˣ x′ ⦂ p
      --------------------
    → Γ≤ ⊢ ` x ≤ᴹ ` x′ ⦂ ⟨ pᵉ ⟩ p
```

The rules for abstraction and application are quantified over precision
witnesses between function types `p : A ⇒ P ≤ A′ ⇒ P′`,
which can be projected to precision witnesses between their domains `dom p : A ≤ A′`
and codomains `P ≤ᶜ P′`. This allows `p` to be either `_⇒_` or `id`.
This lets us use `id` uniformly in the proof of reflexivity for term precision.
```
  ƛ≤ƛ : ∀ {N N′} {e : E ≤ᵉ E′} {p : A ⇒ P ≤ A′ ⇒ P′} {a f b}
    → split⇒ p ≡ (a , f , b)
    → Γ≤ ▷ a ⊢ N ≤ᴹ N′ ⦂ ⟨ f ⟩ b
      ----------------------------
    → Γ≤ ⊢ ƛ N ≤ᴹ ƛ N′ ⦂ ⟨ e ⟩ p

  ·≤· : ∀ {L L′ M M′} {p : A ⇒ P ≤ A′ ⇒ P′} {a e b}
    → split⇒ p ≡ (a , e , b)
    → Γ≤ ⊢ L ≤ᴹ L′ ⦂ ⟨ e ⟩ p
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ e ⟩ a
      -----------------------------
    → Γ≤ ⊢ L · M ≤ᴹ L′ · M′ ⦂ ⟨ e ⟩ b
```

Base types are only related by `id`, which
thus serves as the index for constants and primitive operators.
```
  $≤$ : ∀ {ι} {pᵉ : E ≤ᵉ E′}
    → (k : rep ι)
      ------------------------
    → Γ≤ ⊢ $ k ≤ᴹ $ k ⦂ ⟨ pᵉ ⟩ id

  ⦅⦆≤⦅⦆ : ∀ {ι ι′ ι″ M M′ N N′} {pᵉ : E ≤ᵉ E′}
    → (_⊕_ : rep ι → rep ι′ → rep ι″)
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ pᵉ ⟩ id
    → Γ≤ ⊢ N ≤ᴹ N′ ⦂ ⟨ pᵉ ⟩ id
      -------------------------------------
    → Γ≤ ⊢  M  ⦅ _⊕_ ⦆ N
         ≤ᴹ M′ ⦅ _⊕_ ⦆ N′ ⦂ ⟨ pᵉ ⟩ id
```

Handlers and effects also follow the same pattern of relating subterms.
Precision between `handle` terms uses handler precision `_⊢_≤_⦂_⇒ʰ_` which
will be defined below.
```
  perform≤perform : ∀ {e}
      {e∈E : e ∈☆ E} {e∈E′ : e ∈☆ E′}
      {E≤ : E ≤ᵉ E′} {M M′}
    → {eq : response e ≡ A}
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ id
    → Γ≤ ⊢  perform- e∈E  M  eq
         ≤ᴹ perform- e∈E′ M′ eq ⦂ ⟨ E≤ ⟩ id

  handle≤handle :
      ∀ {P≤ : P ≤ᶜ P′} {Q≤ : Q ≤ᶜ Q′} {H H′ M M′}
    → Γ≤ ⊢ H ≤ H′ ⦂ P≤ ⇒ʰ Q≤
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ P≤
    → Γ≤ ⊢ handle H M ≤ᴹ handle H′ M′ ⦂ Q≤
```

Boxes have type `★`, and their contents have ground types, which
can only be related by precision if they are equal. So the relation
should be witnessed by `id`.
```
  ⇑≤⇑ : ∀ {G E E′ M M′} {pᵉ : E ≤ᵉ E′}
    → (g : Ground G)
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ pᵉ ⟩ id
      -----------------------------
    → Γ≤ ⊢ (M ⇑ g) ≤ᴹ (M′ ⇑ g) ⦂ ⟨ pᵉ ⟩ id
```

`M` is more precise than a box `M′ ⇑ g` if `M` is more precise than the underlying term `M′`.
Note the absence of a symmetric rule where the box is on the left.
Intuitively, a more precisely typed term uses fewer dynamic boxes.
```
  ≤⇑ : ∀ {G M M′} {p : A ≤ G} {pᵉ : E ≤ᵉ E′}
    → (g : Ground G)
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ pᵉ ⟩ p
      --------------------------
    → Γ≤ ⊢ M ≤ᴹ (M′ ⇑ g) ⦂ ⟨ pᵉ ⟩ (p ⇑ g)
```

Term precision does not imply that the more precise side has fewer casts.
Indeed, increasing the precision of a term may introduce more run-time checks.

For instance, consider the identity ``ID = ƛ (` Z) : ∅ ⊢ ★ ⇒ ⟨ ☆ ⟩ ★``,
and the term obtained from casting a monomorphic identity `ID′ = cast (+ p) ID-ℕ`,
where ``ID-ℕ = λ (` Z) : ∅ ⊢ ℕ ⇒ ⟨ ε ⟩ ℕ``. `ID-ℕ` is more precise than `ID`,
and `ID-ℕ` contains a cast while `ID` does not.

Unlike the preceding rules, we will have separate
rules for inserting casts on either side.
When we insert a cast on the left with `cast≤`,
the right-hand side is less precise than the term
on the left-hand side before and after the cast.
This results in a triangle, with vertices `P`, `Q`, `R`, where one side
consists of the cast `P =>ᶜ Q`, and the other two sides are the inequalities
`P ≤ᶜ R` and `Q ≤ᶜ R`. We require that triangle to commute, using the predicate
`commute≤ᶜ`.
```
  cast≤ : ∀ {M : Γ ⊢ ⟨ E ⟩ A} {M′ : Γ′ ⊢ ⟨ E′ ⟩ A′} {e : E ≤ᵉ E′}
      {±p : A => B} {q : B ≤ A′} {r : A ≤ A′}
    → commute≤ ±p q r
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ e ⟩ r
      -------------------------
    → Γ≤ ⊢ cast ±p M ≤ᴹ M′ ⦂ ⟨ e ⟩ q
```

The `≤cast` rule is symmetrical to `cast≤`.
```
  ≤cast : ∀ {M : Γ ⊢ ⟨ E ⟩ A} {M′ : Γ′ ⊢ ⟨ E′ ⟩ A′} {e : E ≤ᵉ E′}
      {p : A ≤ A′} {±q : A′ => B′} {r : A ≤ B′}
    → ≤commute p ±q r
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ e ⟩ p
      -------------------------
    → Γ≤ ⊢ M ≤ᴹ cast ±q M′ ⦂ ⟨ e ⟩ r
```

```
  castᵉ≤ : ∀ {M : Γ ⊢ ⟨ E ⟩ A} {M′ : Γ′ ⊢ ⟨ E′ ⟩ A′} {a : A ≤ A′}
      {e : E ≤ᵉ E′} {±f : E =>ᵉ F} {f′ : F ≤ᵉ E′}
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ e ⟩ a
      -----
    → Γ≤ ⊢ castᵉ ±f M ≤ᴹ M′ ⦂ ⟨ f′ ⟩ a
```

```
  ≤castᵉ : ∀ {M : Γ ⊢ ⟨ E ⟩ A} {M′ : Γ′ ⊢ ⟨ E′ ⟩ A′} {a : A ≤ A′}
      {e : E ≤ᵉ E′} {±f : E′ =>ᵉ F′} {f′ : E ≤ᵉ F′}
    → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ e ⟩ a
      -----
    → Γ≤ ⊢ M ≤ᴹ castᵉ ±f M′ ⦂ ⟨ f′ ⟩ a
```

```
  blame≤ : ∀ {A A′ M′} {p : A ≤ᶜ A′}
      ---------------------
    → Γ≤ ⊢ blame ≤ᴹ M′ ⦂ p
```

A cast between function types eventually steps to a `ƛ-wrap`, so
we add an ad-hoc rule for that construct. After a further `β` step,
the resulting terms will related using `cast≤` for `wrap≤`,
and `≤cast` for `≤wrap`.
```
  wrap≤ :
      {N : Γ ▷ A ⊢ ⟨ E ⟩ B} {N′ : Γ′ ▷ A″ ⊢ ⟨ E″ ⟩ B″}
      {±p : A ⇒ ⟨ E ⟩ B => A′ ⇒ ⟨ E′ ⟩ B′}
      {q : A′ ⇒ ⟨ E′ ⟩ B′ ≤ A″ ⇒ ⟨ E″ ⟩ B″}
      {r : A ⇒ ⟨ E ⟩ B ≤ A″ ⇒ ⟨ E″ ⟩ B″}
      {∓s : A′ => A} {±t : B => B′} {±e : E =>ᵉ E′}
    → split ±p ≡ ∓s ⇒⟨ ±e ⟩ ±t
    → commute≤ ±p q r
    → (∀ {F F′} {f : F ≤ᵉ F′} →
         Γ≤ ⊢ ƛ N ≤ᴹ ƛ N′ ⦂ ⟨ f ⟩ r)
      ------------------------------------------
    → ∀ {F F′} {f : F ≤ᵉ F′} → Γ≤ ⊢ ƛ-wrap ∓s ±t ±e (ƛ N) ≤ᴹ ƛ N′ ⦂ ⟨ f ⟩ q
```

Here is an example reduction sequence (with some oversimplifications for conciseness)
of an abstraction `ƛ N` under a cast applied to an argument `M`.
Every term in this sequence is more precise than `(ƛ N′) · M′`
given `ƛ N ≤ᴹ ƛ N′` and `M ≤ᴹ M′`. This is witnessed by `cast≤` for the first
term, `wrap≤` for the second term, and a combination of `cast≤` and `·≤·` for
the last term.

                          cast ±p (ƛ N) · M
    —→               ƛ-wrap ∓s ±t (ƛ N) · M
    =   (ƛ (cast ±t (lift (ƛ N)
                     · cast ∓s (` Z)))) · M
    —→           cast ±t ((ƛ N) · cast ∓s M)

```
  ≤wrap :
      {N : Γ ▷ A ⊢ ⟨ E ⟩ B} {N′ : Γ′ ▷ A′ ⊢ ⟨ E′ ⟩ B′}
      {p : A ⇒ ⟨ E ⟩ B ≤ A′ ⇒ ⟨ E′ ⟩ B′}
      {±q : A′ ⇒ ⟨ E′ ⟩ B′ => A″ ⇒ ⟨ E″ ⟩ B″}
      {r : A ⇒ ⟨ E ⟩ B ≤ A″ ⇒ ⟨ E″ ⟩ B″}
      {∓s : A″ => A′} {±t : B′ => B″} {±e : E′ =>ᵉ E″}
    → split ±q ≡ ∓s ⇒⟨ ±e ⟩ ±t
    → ≤commute p ±q r
    → (∀ {F F′} {f : F ≤ᵉ F′} → Γ≤ ⊢ ƛ N ≤ᴹ ƛ N′ ⦂ ⟨ f ⟩ p)
      -----------------------------------------------------
    → ∀ {F F′} {f : F ≤ᵉ F′} → Γ≤ ⊢ ƛ N ≤ᴹ ƛ-wrap ∓s ±t ±e (ƛ N′) ⦂ ⟨ f ⟩ r
```

Precision between the operation clauses of handlers.
```
On-Perform :
    ∀ (Γ≤ : Γ ≤ᴳ Γ′) (Q≤ : Q ≤ᶜ Q′) → ∀ {Eh Eh′}
  → Core.On-Perform Γ Q Eh
  → Core.On-Perform Γ′ Q′ Eh′ → Set
On-Perform Γ≤ Q≤
  = All₂′ λ M M′ →
      ∃[ B⇒Q≤ ] dom B⇒Q≤ ≡ id ×
                ⟨ eff B⇒Q≤ ⟩ cod B⇒Q≤ ≡ Q≤ ×
                (Γ≤ ▷ id ▷ (B⇒Q≤) ⊢ M ≤ᴹ M′ ⦂ Q≤)
```

Precision between handlers.
```
record _⊢_≤_⦂_⇒ʰ_ Γ≤ {P P′ Q Q′} H H′ P≤ Q≤ where
  inductive
  open _≤ᶜ_ using (returns)
  field
    on-return :
      Γ≤ ▷ returns P≤ ⊢ on-return H ≤ᴹ on-return H′ ⦂ Q≤
    on-perform :
      On-Perform Γ≤ Q≤ (on-perform H) (on-perform H′)

open _⊢_≤_⦂_⇒ʰ_ public
```

Term precision is reflexive. Because term precision is indexed by context precision and type precision,
its reflexivity proof will be indexed by their respective reflexivity proofs.

\iffalse
```
{-
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
-}
```
\fi

## Cast congruence

Term precision does not contain a rule to insert a cast on
both sides of an inequation at once.
The following lemmas derive such rules when both sides are casts with the same polarity.

```
data square {A A′ B B′} (a : A ≤ A′) (b : B ≤ B′) : A => B → A′ => B′ → Set where
  square+ : ∀ {p q} → p ⨟ b ≡ a ⨟ q → square a b (+ p) (+ q)
  square- : ∀ {p q} → b ⨟ q ≡ p ⨟ a → square a b (- p) (- q)

square-refl : ∀ (p : A => B) → square id id p p
square-refl (+ p) = square+ (sym (left-id p))
square-refl (- p) = square- (left-id p)

cast≤cast : ∀ {M : Γ ⊢ ⟨ E ⟩ A} {M′ : Γ′ ⊢ ⟨ E′ ⟩ A′} {Γ≤ : Γ ≤ᴳ Γ′}
    {a : A ≤ A′} {b : B ≤ B′} {p q} {e}
  → square a b p q
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ e ⟩ a
    -----
  → Γ≤ ⊢ cast p M ≤ᴹ cast q M′ ⦂ ⟨ e ⟩ b
cast≤cast (square+ comm) M≤M′ = cast≤ comm (≤cast refl M≤M′)
cast≤cast (square- comm) M≤M′ = ≤cast comm (cast≤ refl M≤M′)

data squareᵉ {E E′ F F′} : E =>ᵉ F → E′ =>ᵉ F′ → Set where
  square+ : ∀ {p q} → squareᵉ (+ p) (+ q)
  square- : ∀ {p q} → squareᵉ (- p) (- q)

squareᵉ-refl : ∀ (p : E =>ᵉ F) → squareᵉ p p
squareᵉ-refl (+ p) = square+
squareᵉ-refl (- p) = square-

castᵉ≤castᵉ : ∀ {M : Γ ⊢ ⟨ E ⟩ A} {M′ : Γ′ ⊢ ⟨ E′ ⟩ A′} {Γ≤ : Γ ≤ᴳ Γ′}
    {a : A ≤ A′} {e : E ≤ᵉ E′} {f : F ≤ᵉ F′} {p q}
  → squareᵉ p q
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ e ⟩ a
    -----
  → Γ≤ ⊢ castᵉ p M ≤ᴹ castᵉ q M′ ⦂ ⟨ f ⟩ a
castᵉ≤castᵉ {e = e} (square+ {q = q}) M≤M′ = castᵉ≤ {e = e ⨟ᵉ q} (≤castᵉ M≤M′)
castᵉ≤castᵉ {e = e} (square- {p = p}) M≤M′ = ≤castᵉ {e = p ⨟ᵉ e} (castᵉ≤ M≤M′)
```

\iffalse
TODO: The above is a refactoring of the code below,
preserved for the associated comments.
```
-- Upcast congruence:
-- ```
-- +≤+  : {M : Γ ⊢ P} {M′ : Γ′ ⊢ P′} {Γ≤ : Γ ≤ᴳ Γ′}
--      {p : P ≤ᶜ Q} {q : P′ ≤ᶜ Q′}
--      {s : P ≤ᶜ P′} {t : Q ≤ᶜ Q′}
--   →  p ⨟ᶜ t ≡ s ⨟ᶜ q
--   →  Γ≤ ⊢ M ≤ᴹ M′ ⦂ s
--      ------------------------------------
--   →  Γ≤ ⊢ cast (+ p) M ≤ᴹ cast (+ q) M′ ⦂ t
-- +≤+ e M≤M′ = cast≤ e (≤cast refl M≤M′)
-- ```
--
-- Here is the derivation of upcast congruence:
--
--     Γ≤ ⊢ M ≤ᴹ M′ ⦂ s
--     s ⨟ q ≡ r
--     ---------------------- ≤+
--     Γ≤ ⊢ M ≤ᴹ (cast (+ q) M′) ⦂ r
--     p ⨟ t ≡ r
--     ---------------------------- +≤
--     Γ≤ ⊢ (cast (+ p) M) ≤ᴹ (cast (+ q) M′) ⦂ t
--
-- Here it is illustrated:
--
--                              s
--                    M : A    ---→           M′ : A′
--                      |       \                |
--                    p |      r \               | q
--                      -         ↘              -
--       (cast (+ p) M) : B ---→ (cast (+ q) M′) : B′
--                           t
--
-- Downcast congruence:
-- ```
-- -≤- : {Γ≤ : Γ ≤ᴳ Γ′}
--     {M : Γ ⊢ Q} {M′ : Γ′ ⊢ Q′}
--     {p : P ≤ᶜ Q} {q : P′ ≤ᶜ Q′}
--     {s : P ≤ᶜ P′} {t : Q ≤ᶜ Q′}
--   → s ⨟ᶜ q ≡ p ⨟ᶜ t
--   → Γ≤ ⊢ M ≤ᴹ M′ ⦂ t
--     --------------------------------------
--   → Γ≤ ⊢  cast (- p) M
--        ≤ᴹ cast (- q) M′ ⦂ s
-- -≤- e M≤M′ = ≤cast e (cast≤ refl M≤M′)
-- ```
--
-- Here is the derivation of downcast congruence:
--
--     Γ≤ ⊢ M ≤ᴹ M′ ⦂ t
--     p ⨟ t ≡ r
--     ---------------------- ≤+
--     Γ≤ ⊢ (cast (- p) M) ≤ᴹ M′ ⦂ r
--     s ⨟ q ≡ r
--     ---------------------------- +≤
--     Γ≤ ⊢ (cast (- p) M) ≤ᴹ (cast (- q) M′) ⦂ t
--
-- Here it is illustrated:
--
--                              s
--                    M : A    ---→           M′ : A′
--                      -       \                -
--                    p |      r \               | q
--                      |         ↘              |
--       (cast (- p) M) : B ---→ (cast (- q) M′) : B′
--                           t
```
\fi

## Reflexivity of term precision

Every term is at least as precise as itself.
Term precision is indexed by a type precision proof,
and to relate a term with itself, a natural choice is to
index it by the reflexivity proof `id` (or `⟨ id ⟩ id` which is the reflexivity
proof for computation type precision). Reflexivity depends crucially on the
fact that the rules for abstraction `ƛ≤ƛ`, application `·≤·`, and handlers
`handle≤handle` are parameterized by proofs for type precision on functions,
instead of constructing them using `_⇒_` which is distinct from `id`.

\iffalse
```
reflˣ : ∀ {Γ A}
    → (x : Γ ∋ A)
      -------------------
    → idᴳ ⊢ x ≤ˣ x ⦂ id
reflˣ Z      =  Z≤Z
reflˣ (S x)  =  S≤S (reflˣ x)
```

```
reflʰ : ∀ {Γ P Q}
  → (H : Γ ⊢ P ⇒ʰ Q)
  → idᴳ ⊢ H ≤ H ⦂ ⟨ id ⟩ id ⇒ʰ ⟨ id ⟩ id
```
\fi

```
reflᴹ : ∀ {Γ P}
    → (M : Γ ⊢ P)
      -------------------
    → idᴳ ⊢ M ≤ᴹ M ⦂ ⟨ id ⟩ id
```

\iffalse
```
reflᴹ (` x)           =  `≤` (reflˣ x)
reflᴹ (ƛ M)           =  ƛ≤ƛ refl (reflᴹ M)
reflᴹ (L · M)         =  ·≤· refl (reflᴹ L) (reflᴹ M)
reflᴹ ($ k)           =  $≤$ k
reflᴹ (M ⦅ _⊕_ ⦆ N)   =  ⦅⦆≤⦅⦆ _⊕_ (reflᴹ M)
                                   (reflᴹ N)
reflᴹ (M ⇑ g)         =  ⇑≤⇑ g (reflᴹ M)
reflᴹ (cast p M)      =  cast≤cast (square-refl p) (reflᴹ M)
reflᴹ (castᵉ p M)     =  castᵉ≤castᵉ (squareᵉ-refl p) (reflᴹ M)
reflᴹ blame           =  blame≤
reflᴹ (perform- e∈E M eq)
  =  perform≤perform (reflᴹ M)
reflᴹ (handle H M)
  =  handle≤handle (reflʰ H) (reflᴹ M)

reflʰ H = record
  { on-return = reflᴹ (H .on-return)
  ; on-perform = refl-on-perform (H .on-perform) }
  where
    refl-on-perform : ∀ {Eh} Ms →
      On-Perform _ _ {Eh = Eh} Ms Ms
    refl-on-perform [] = []
    refl-on-perform (M ∷ Ms)
      = (refl , id , refl , refl , reflᴹ M)
        ∷ refl-on-perform Ms
```
\fi

\iffalse
## Precision is preserved by substitution

Precision on renamings and substitutions.

```
infix 4 _→ᴿ_∋_≤_ _→ˢ_∋_≤_ _→ᵀ_∋_≤_

_→ᴿ_∋_≤_ : (Γ≤ : Γ ≤ᴳ Γ′) (Δ≤ : Δ ≤ᴳ Δ′)
  → (Γ →ᴿ Δ) → (Γ′ →ᴿ Δ′) → Set
Γ≤ →ᴿ Δ≤ ∋ ρ ≤ ρ′
  = ∀ {A A′} {A≤ : A ≤ A′} {x x′}
  → Γ≤ ⊢ x ≤ˣ x′ ⦂ A≤
    -----------------------
  → Δ≤ ⊢ ρ x ≤ˣ ρ′ x′ ⦂ A≤

_→ˢ_∋_≤_ : (Γ≤ : Γ ≤ᴳ Γ′) (Δ≤ : Δ ≤ᴳ Δ′)
  → (Γ →ˢ Δ) → (Γ′ →ˢ Δ′) → Set
Γ≤ →ˢ Δ≤ ∋ σ ≤ σ′
  = ∀ {A A′} {A≤ : A ≤ A′}
      {E E′} {E≤ : E ≤ᵉ E′} {x x′}
  → Γ≤ ⊢ x ≤ˣ x′ ⦂ A≤
    -----------------------
  → Δ≤ ⊢ σ x ≤ᴹ σ′ x′ ⦂ ⟨ E≤ ⟩ A≤

_→ᵀ_∋_≤_ : (Γ≤ : Γ ≤ᴳ Γ′) (Δ≤ : Δ ≤ᴳ Δ′)
  → (Γ →ᵀ Δ) → (Γ′ →ᵀ Δ′) → Set
Γ≤ →ᵀ Δ≤ ∋ s ≤ s′
  = ∀ {A A′} {A≤ : A ≤ A′}
      {E E′} {E≤ : E ≤ᵉ E′} {M M′}
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ A≤
    -----------------------
  → Δ≤ ⊢ s M ≤ᴹ s′ M′ ⦂ ⟨ E≤ ⟩ A≤
```
\fi

\iffalse

### Renaming {#renaming-prec}

Extension
```
ren▷≤ : ∀ {Γ Γ′ Δ Δ′} {Γ≤ : Γ ≤ᴳ Γ′} {Δ≤ : Δ ≤ᴳ Δ′} {ρ : Γ →ᴿ Δ} {ρ′ : Γ′ →ᴿ Δ′}
  → Γ≤ →ᴿ Δ≤ ∋ ρ ≤ ρ′
    ------------------------------------------------------
  → ∀ {A A′} {A≤ : A ≤ A′} → Γ≤ ▷ A≤ →ᴿ Δ≤ ▷ A≤ ∋ ren▷ ρ ≤ ren▷ ρ′
ren▷≤ ρ≤ Z≤Z       =  Z≤Z
ren▷≤ ρ≤ (S≤S x≤)  =  S≤S (ρ≤ x≤)
```

```
ren∘ƛ-wrap : ∀ {Γ Δ A A′ E E′ F} {∓s : A′ => A} {±t : B => B′} {±e : E =>ᵉ E′}
    (ρ : Γ →ᴿ Δ) (M : ∀ {F} → Γ ⊢ ⟨ F ⟩ (A ⇒ ⟨ E ⟩ B))
  → ren ρ (ƛ-wrap ∓s ±t ±e M {F = F}) ≡ ƛ-wrap ∓s ±t ±e (ren ρ M)
ren∘ƛ-wrap {A′ = A′} {E = E} {∓s = ∓s} {±t} ρ M
  rewrite (lift∘ren {A = A′} ρ (M {E})) = refl

sub∘ƛ-wrap : ∀ {Γ Δ A A′ E E′ F} {∓s : A′ => A} {±t : B => B′} {±e : E =>ᵉ E′}
    (σ : Γ →ˢ Δ) (M : ∀ {F} → Γ ⊢ ⟨ F ⟩ (A ⇒ ⟨ E ⟩ B))
  → sub σ (ƛ-wrap ∓s ±t ±e M {F = F}) ≡ ƛ-wrap ∓s ±t ±e (sub σ M)
sub∘ƛ-wrap {A′ = A′} {E = E} {∓s = ∓s} {±t} σ M
  rewrite (lift∘sub {A = A′} σ (M {E})) = refl
```

Preservation of precision under renaming
```
ren≤ʰ : ∀ {Γ Γ′ Δ Δ′} {Γ≤ : Γ ≤ᴳ Γ′} {Δ≤ : Δ ≤ᴳ Δ′} {ρ : Γ →ᴿ Δ} {ρ′ : Γ′ →ᴿ Δ′}
  → Γ≤ →ᴿ Δ≤ ∋ ρ ≤ ρ′
    -------------------------------------------
  → (∀ {P P′ Q Q′} {P≤ : P ≤ᶜ P′} {Q≤ : Q ≤ᶜ Q′} {H H′}
      → Γ≤ ⊢ H ≤ H′ ⦂ P≤ ⇒ʰ Q≤
      → Δ≤ ⊢ renʰ ρ H ≤ renʰ ρ′ H′ ⦂ P≤ ⇒ʰ Q≤)

ren≤ : ∀ {Γ Γ′ Δ Δ′} {Γ≤ : Γ ≤ᴳ Γ′} {Δ≤ : Δ ≤ᴳ Δ′} {ρ : Γ →ᴿ Δ} {ρ′ : Γ′ →ᴿ Δ′}
  →  Γ≤ →ᴿ Δ≤ ∋ ρ ≤ ρ′
    -------------------------------------------
  → (∀ {A A′} {A≤ : A ≤ A′} {E E′} {E≤ : E ≤ᵉ E′} {M M′}
      → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ A≤
      → Δ≤ ⊢ ren ρ M ≤ᴹ ren ρ′ M′ ⦂ ⟨ E≤ ⟩ A≤)
ren≤ ρ≤ (`≤` x)              =  `≤` (ρ≤ x)
ren≤ ρ≤ (ƛ≤ƛ split≡ N≤)             =  ƛ≤ƛ split≡ (ren≤ (ren▷≤ ρ≤) N≤)
ren≤ ρ≤ (·≤· split≡ L≤ M≤)          =  ·≤· split≡ (ren≤ ρ≤ L≤) (ren≤ ρ≤ M≤)
ren≤ ρ≤ ($≤$ k)              =  $≤$ k
ren≤ ρ≤ (⦅⦆≤⦅⦆ _⊕_ M≤ N≤)    =  ⦅⦆≤⦅⦆ _⊕_ (ren≤ ρ≤ M≤) (ren≤ ρ≤ N≤)
ren≤ ρ≤ (⇑≤⇑ g M≤)           =  ⇑≤⇑ g (ren≤ ρ≤ M≤)
ren≤ ρ≤ (≤⇑ g M≤)            =  ≤⇑ g (ren≤ ρ≤ M≤)
ren≤ ρ≤ (cast≤ e M≤)         =  cast≤ e (ren≤ ρ≤ M≤)
ren≤ ρ≤ (≤cast e M≤)         =  ≤cast e (ren≤ ρ≤ M≤)
ren≤ ρ≤ (castᵉ≤ M≤)        =  castᵉ≤ (ren≤ ρ≤ M≤)
ren≤ ρ≤ (≤castᵉ M≤)        =  ≤castᵉ (ren≤ ρ≤ M≤)
ren≤ ρ≤ blame≤               =  blame≤
ren≤ {ρ = ρ} ρ≤ {A≤ = A≤} {E = E}
  (wrap≤ {N = N} {∓s = ∓s} {±t} {±e} i e ƛN≤ƛN′)
  rewrite ren∘ƛ-wrap {F = E} {∓s = ∓s} {±t = ±t} {±e = ±e} ρ (ƛ N)
  = wrap≤ i e (ren≤ ρ≤ ƛN≤ƛN′)
ren≤ {ρ′ = ρ′} ρ≤ {A≤ = A≤} {E′ = E′}
  (≤wrap {N′ = N′} {∓s = ∓s} {±t} {±e} i e ƛN≤ƛN′)
  rewrite ren∘ƛ-wrap {F = E′} {∓s = ∓s} {±t = ±t} {±e = ±e} ρ′ (ƛ N′)
  = ≤wrap i e (ren≤ ρ≤ ƛN≤ƛN′)
ren≤ ρ≤ (perform≤perform M≤) = perform≤perform (ren≤ ρ≤ M≤)
ren≤ ρ≤ (handle≤handle H≤ M≤) = handle≤handle (ren≤ʰ ρ≤ H≤) (ren≤ ρ≤ M≤)

ren≤ʰ ρ≤ H≤ = record
  { on-return = ren≤ (ren▷≤ ρ≤) (on-return H≤)
  ; on-perform = ren≤-on-perform (on-perform H≤) }
  where
    open _⊢_≤_⦂_⇒ʰ_

    ren≤-on-perform : ∀ {Eh Eh′ Ms Ms′}
      → On-Perform _ _ {Eh} {Eh′} Ms Ms′
      → On-Perform _ _ (ren-on-perform _ Ms) (ren-on-perform _ Ms′)
    ren≤-on-perform [] = []
    ren≤-on-perform ((refl , B⇒Q≤ , dom≡ , cod≡ , M≤) ∷ Ms≤)
      = (refl , B⇒Q≤ , dom≡ , cod≡ , ren≤ (ren▷≤ (ren▷≤ ρ≤)) M≤) ∷ ren≤-on-perform Ms≤
```

```
lift≤ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᴳ Γ′} {B B′} {B≤ : B ≤ B′}
          {A A′} {A≤ : A ≤ A′} {E E′} {E≤ : E ≤ᵉ E′} {M M′}
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ A≤
    ---------------------------------------
  → Γ≤ ▷ B≤ ⊢ lift M ≤ᴹ lift M′ ⦂ ⟨ E≤ ⟩ A≤
lift≤ = ren≤ S≤S

lift≤ʰ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᴳ Γ′} {A A′} {A≤ : A ≤ A′}
          {P P′ Q Q′} {P≤ : P ≤ᶜ P′} {Q≤ : Q ≤ᶜ Q′} {H H′}
  → Γ≤ ⊢ H ≤ H′ ⦂ P≤ ⇒ʰ Q≤
    --------------------------------------
  → Γ≤ ▷ A≤ ⊢ liftʰ H ≤ liftʰ H′ ⦂ P≤ ⇒ʰ Q≤
lift≤ʰ = ren≤ʰ S≤S
```

### Substitution {#substitution-prec}

Extension
```
sub▷≤ : ∀ {Γ Γ′ Δ Δ′} {Γ≤ : Γ ≤ᴳ Γ′} {Δ≤ : Δ ≤ᴳ Δ′} {σ : Γ →ˢ Δ} {σ′ : Γ′ →ˢ Δ′}
  → Γ≤ →ˢ Δ≤ ∋ σ ≤ σ′
    ------------------------------------------------------
  → ∀ {A A′} {A≤ : A ≤ A′} → Γ≤ ▷ A≤ →ˢ Δ≤ ▷ A≤ ∋ sub▷ σ ≤ sub▷ σ′
sub▷≤ σ≤ Z≤Z       =  `≤` Z≤Z
sub▷≤ σ≤ (S≤S x≤)  =  ren≤ S≤S (σ≤ x≤)
```

\fi

\iffalse
Preservation of precision under substitution
```
sub≤ : {σ : Γ →ˢ Δ} {σ′ : Γ′ →ˢ Δ′}
     → Γ≤ →ˢ Δ≤ ∋ σ ≤ σ′
       -------------------------
     → Γ≤ →ᵀ Δ≤ ∋ sub σ ≤ sub σ′
```
\fi

\iffalse
```
sub≤ σ≤ (`≤` x)              =  σ≤ x
sub≤ σ≤ (ƛ≤ƛ split≡ N≤)             =  ƛ≤ƛ split≡ (sub≤ (sub▷≤ σ≤) N≤)
sub≤ σ≤ (·≤· split≡ L≤ M≤)          =  ·≤· split≡ (sub≤ σ≤ L≤) (sub≤ σ≤ M≤)
sub≤ σ≤ ($≤$ k)              =  $≤$ k
sub≤ σ≤ (⦅⦆≤⦅⦆ _⊕_ M≤ N≤)    =  ⦅⦆≤⦅⦆ _⊕_ (sub≤ σ≤ M≤) (sub≤ σ≤ N≤)
sub≤ σ≤ (⇑≤⇑ g M≤)           =  ⇑≤⇑ g (sub≤ σ≤ M≤)
sub≤ σ≤ (≤⇑ g M≤)            =  ≤⇑ g (sub≤ σ≤ M≤)
sub≤ σ≤ (cast≤ e M≤)         =  cast≤ e (sub≤ σ≤ M≤)
sub≤ σ≤ (≤cast e M≤)         =  ≤cast e (sub≤ σ≤ M≤)
sub≤ σ≤ (castᵉ≤ M≤)          =  castᵉ≤ (sub≤ σ≤ M≤)
sub≤ σ≤ (≤castᵉ M≤)          =  ≤castᵉ (sub≤ σ≤ M≤)
sub≤ σ≤ blame≤               =  blame≤
sub≤ {σ = σ} σ≤ {E = E} (wrap≤ {N = N} {∓s = ∓s} {±t} {±e} i e ƛN≤ƛN′)
  rewrite sub∘ƛ-wrap {F = E} {∓s = ∓s} {±t} {±e} σ (ƛ N)
  =  wrap≤ i e (sub≤ σ≤ ƛN≤ƛN′)
sub≤ {σ′ = σ′} σ≤ {E′ = E′} (≤wrap {N′ = N′} {∓s = ∓s} {±t} {±e} i e ƛN≤ƛN′)
  rewrite sub∘ƛ-wrap {F = E′} {∓s = ∓s} {±t} {±e} σ′ (ƛ N′)
  =  ≤wrap i e (sub≤ σ≤ ƛN≤ƛN′)
sub≤ σ≤ (perform≤perform M≤) = perform≤perform (sub≤ σ≤ M≤)
sub≤ σ≤ (handle≤handle H≤ M≤) = handle≤handle sub≤ʰ (sub≤ σ≤ M≤)
  where
    open _⊢_≤_⦂_⇒ʰ_

    sub≤-on-perform : ∀ {Eh Eh′ Ms Ms′}
      → On-Perform _ _ {Eh} {Eh′} Ms Ms′
      → On-Perform _ _ (sub-on-perform _ Ms) (sub-on-perform _ Ms′)
    sub≤-on-perform [] = []
    sub≤-on-perform ((refl , B⇒Q≤ , dom≡ , cod≡ , M≤) ∷ Ms≤)
      = (refl , B⇒Q≤ , dom≡ , cod≡ , sub≤ (sub▷≤ (sub▷≤ σ≤)) M≤) ∷ sub≤-on-perform Ms≤

    sub≤ʰ = record
      { on-return = sub≤ (sub▷≤ σ≤) (on-return H≤)
      ; on-perform = sub≤-on-perform (on-perform H≤) }
```
\fi

\iffalse
Preservation of precision under substitution, special case for beta

```
σ₀≤σ₀ :
    {M : ∀ {E} → Γ ⊢ ⟨ E ⟩ A}
    {M′ : ∀ {E′} → Γ′ ⊢ ⟨ E′ ⟩ A′}
    {Γ≤ : Γ ≤ᴳ Γ′} {s : A ≤ A′}
  → (∀ {E E′} {E≤ : E ≤ᵉ E′}
       → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ s)
  → Γ≤ ▷ s →ˢ Γ≤ ∋ σ₀ M ≤ σ₀ M′
σ₀≤σ₀ M≤M′ Z≤Z         =  M≤M′
σ₀≤σ₀ M≤M′ (S≤S x≤x′)  =  `≤` x≤x′

[]≤[] : ∀ {N N′} {M : ∀ {E} → Γ ⊢ ⟨ E ⟩ A}
          {M′ : ∀ {E′} → Γ′ ⊢ ⟨ E′ ⟩ A′}
          {Γ≤ : Γ ≤ᴳ Γ′} {s : A ≤ A′}
          {t : B ≤ B′} {E≤ : E ≤ᵉ E′}
        → Γ≤ ▷ s ⊢ N ≤ᴹ N′ ⦂ ⟨ E≤ ⟩ t
        → (∀ {E E′} {E≤ : E ≤ᵉ E′}
             → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ s)
          -----------------------------
        → Γ≤ ⊢ N [ M ] ≤ᴹ N′ [ M′ ] ⦂ ⟨ E≤ ⟩ t
[]≤[] N≤N′ M≤M′ =  sub≤ (σ₀≤σ₀ M≤M′) N≤N′
```

## Relating a term to its type erasure

```
-- ƛ≤ƛ★ : ∀ {N N′} {Γ≤ : Γ ≤ᴳ Γ′}
--          {F≤ : F ≤ᵉ F′}
--          {p : A ⇒ ⟨ E ⟩ B ≤ ★ ⇒ ⟨ ☆ ⟩ ★}
--   → Γ≤ ▷ dom p ⊢ N ≤ᴹ N′ ⦂ cod p
--     ----------------------------
--   → Γ≤ ⊢ ƛ N ≤ᴹ ƛ★ N′ ⦂ ⟨ F≤ ⟩ (p ⇑ ★⇒★)
-- ƛ≤ƛ★ N≤N′ = ≤cast refl (ƛ≤ƛ N≤N′)
--
-- ·≤·★ : ∀ {L L′ M M′} {Γ≤ : Γ ≤ᴳ Γ′}
--          {p : A ⇒ ⟨ E ⟩ B ≤ ★ ⇒ ⟨ ☆ ⟩ ★}
--     (let ⟨ E≤ ⟩ _ = cod p)
--   → Γ≤ ⊢ L ≤ᴹ L′ ⦂ ⟨ E≤ ⟩ (p ⇑ ★⇒★)
--   → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ dom p
--     ------------------------------
--   → Γ≤ ⊢ L · M ≤ᴹ L′ ·★ M′ ⦂ cod p
-- ·≤·★ L≤L′ M≤M′ = ·≤· (≤cast refl L≤L′) M≤M′
--
-- $≤$★ : ∀ {ι} {E≤ : E ≤ᵉ ☆} (k : rep ι)
--   → Γ≤ ⊢ $ k ≤ᴹ $★ k ⦂ ⟨ E≤ ⟩ (ι ≤★)
-- $≤$★ {ι = ι} k  =  ≤⇑ ($ ι) ($≤$ k)
--
-- ⦅⦆≤⦅⦆★ : ∀ {ι ι′ ι″ M M′ N N′} {E≤ : E ≤ᵉ ☆}
--   → (_⊕_ : rep ι → rep ι′ → rep ι″)
--   → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ (ι ≤★)
--   → Γ≤ ⊢ N ≤ᴹ N′ ⦂ ⟨ E≤ ⟩ (ι′ ≤★)
--     -------------------------------------
--   → Γ≤ ⊢  M  ⦅ _⊕_ ⦆  N
--        ≤ᴹ M′ ⦅ _⊕_ ⦆★ N′ ⦂ ⟨ E≤ ⟩ (ι″ ≤★)
-- ⦅⦆≤⦅⦆★ _⊕_ M≤M′ N≤N′
--   = ≤cast refl (⦅⦆≤⦅⦆ _⊕_ (≤cast refl M≤M′)
--                           (≤cast refl N≤N′))
--
-- ⌈_⌉≤ᴳ : ∀ (Γ : Context) → Γ ≤ᴳ ⌈ Γ ⌉ᴳ
-- ⌈ ∅ ⌉≤ᴳ          =  ∅
-- ⌈ Γ ▷ A ⌉≤ᴳ      =  ⌈ Γ ⌉≤ᴳ ▷ A≤★
--
-- ⌈_⌉≤ˣ : ∀ {Γ A} → (x : Γ ∋ A) → ⌈ Γ ⌉≤ᴳ ⊢ x ≤ˣ ⌈ x ⌉ˣ ⦂ A≤★
-- ⌈ Z ⌉≤ˣ          =  Z≤Z
-- ⌈ S x ⌉≤ˣ        =  S≤S ⌈ x ⌉≤ˣ
--
-- ⌈_⌉≤ : {M : Γ ⊢ ⟨ E ⟩ A}
--   → (m : Static M)
--   → ⌈ Γ ⌉≤ᴳ ⊢ M ≤ᴹ ⌈ m ⌉ ⦂ ⟨ E≤☆ ⟩ A≤★
-- ⌈ ` x ⌉≤         =  `≤` ⌈ x ⌉≤ˣ
-- ⌈ ƛ N ⌉≤         =  ƛ≤ƛ★ ⌈ N ⌉≤
-- ⌈ L · M ⌉≤       =  ·≤·★ ⌈ L ⌉≤ ⌈ M ⌉≤
-- ⌈ $ k ⌉≤         =  $≤$★ k
-- ⌈ M ⦅ _⊕_ ⦆ N ⌉≤  =  ⦅⦆≤⦅⦆★ _⊕_ ⌈ M ⌉≤ ⌈ N ⌉≤
-- ```
--
-- ## Example {#example-prec}
--
-- ```
-- inc≤inc★ : ∅ ⊢ inc ≤ᴹ inc★ ⦂ ⟨ ε≤☆ ⟩ ℕ⇒ℕ≤★
-- inc≤inc★ = ⌈ Inc ⌉≤
--
-- inc≤inc★′ : ∅ ⊢ inc ≤ᴹ inc★′ ⦂ ⟨ ε≤☆ ⟩ ℕ⇒ℕ≤★
-- inc≤inc★′ = ≤cast refl (reflᴹ inc)
--
-- inc2≤inc★2★ :
--   ∅ ⊢  inc · ($ 2)
--     ≤ᴹ inc★ ·★ ($★ 2) ⦂ ⟨ ε≤☆ ⟩ ℕ≤★
-- inc2≤inc★2★ = ⌈ Inc · ($ 2) ⌉≤
--
-- inc2≤inc★′2★ :
--   ∅ ⊢  inc · ($ 2)
--     ≤ᴹ inc★′ ·★ ($★ 2) ⦂ ⟨ ε≤☆ ⟩ ℕ≤★
-- inc2≤inc★′2★ = ·≤·★ inc≤inc★′ ($≤$★ 2)
```
\fi

## Precision on frames

In the graduality proof, in the case for the rule `handle-perform`,
we have a relation `M ≤ᴹ M′` where `M` is of the form
`handle H (ℰ [ perform e V ])`. This implies that `M′` is also
of that form `handle H′ (ℰ′ [ perform e V′ ])`, with
`H ≤ʰ H′`, `ℰ ≤ ℰ′`, and `V ≤ᴹ V′`. Thus, we need to define precision
on frames `ℰ ≤ ℰ′`, whose rules can be derived from the rules
of precision on terms.

```
infix 3 _⊢_⇒ᶠ_∋_≤_

data _⊢_⇒ᶠ_∋_≤_ {Γ Γ′} (Γ≤ : Γ ≤ᴳ Γ′)
                {P P′} (P≤ : P ≤ᶜ P′)
            : ∀ {Q Q′} (Q≤ : Q ≤ᶜ Q′)
            →            Frame Γ P Q
            →            Frame Γ′ P′ Q′
            → Set where
  □ : Γ≤ ⊢ P≤ ⇒ᶠ P≤ ∋ □ ≤ □

  by_[_]·_ : ∀ {ℰ ℰ′} {M M′}
      {p : A ⇒ ⟨ E ⟩ B ≤ A′ ⇒ ⟨ E′ ⟩ B′} {e a b}
    → split⇒ p ≡ (a , e , b)
    → (ℰ≤ : Γ≤ ⊢ P≤ ⇒ᶠ ⟨ e ⟩ p ∋ ℰ ≤ ℰ′)
    → (M≤ : Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ e ⟩ a)
      ----------------------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ e ⟩ b ∋ [ ℰ ]· M ≤ [ ℰ′ ]· M′

  by_,_·[_] : ∀ {V V′} {ℰ ℰ′}
      {p : A ⇒ ⟨ E ⟩ B ≤ A′ ⇒ ⟨ E′ ⟩ B′} {e a b}
    → split⇒ p ≡ (a , e , b)
    → ((v , v′ , _) :
         Value V × Value V′ ×
         (Γ≤ ⊢ V ≤ᴹ V′ ⦂ ⟨ e ⟩ p))
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ e ⟩ a ∋ ℰ ≤ ℰ′
      -----------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ e ⟩ b ∋ v ·[ ℰ ] ≤ v′ ·[ ℰ′ ]

  [_]⦅_⦆_ : ∀ {ι ι′ ι″} {ℰ ℰ′} {M M′}
    → (ℰ≤ : Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id ∋ ℰ ≤ ℰ′)
    → (f : rep ι → rep ι′ → rep ι″)
    → (M≤ : Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ id)
      ------------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id ∋ [ ℰ ]⦅ f ⦆ M ≤ [ ℰ′ ]⦅ f ⦆ M′

  _⦅_⦆[_] : ∀ {ι ι′ ι″} {V V′} {ℰ ℰ′}
    → ((v , v′ , _) :
         Value V × Value V′ ×
         (Γ≤ ⊢ V ≤ᴹ V′ ⦂ ⟨ E≤ ⟩ id))
    → (f : rep ι → rep ι′ → rep ι″)
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id ∋ ℰ ≤ ℰ′
      ----------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id ∋ v ⦅ f ⦆[ ℰ ] ≤ v′ ⦅ f ⦆[ ℰ′ ]

  [_]⇑_ : ∀ {G ℰ ℰ′}
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id ∋ ℰ ≤ ℰ′
    → (g : Ground G)
      -------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id
         ∋ [ ℰ ]⇑ g ≤ [ ℰ′ ]⇑ g

  ≤⇑ : ∀ {G} {A≤G : A′ ≤ G}
         {g : Ground G} {ℰ ℰ′}
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ A≤G ∋ ℰ ≤ ℰ′
      ---------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ (A≤G ⇑ g)
         ∋ ℰ ≤ [ ℰ′ ]⇑ g

  cast≤ : ∀ {ℰ ℰ′} {e : E ≤ᵉ E′}
      {±p : A => B} {q : B ≤ A′} {r : A ≤ A′}
    → commute≤ ±p q r
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ e ⟩ r ∋ ℰ ≤ ℰ′
      -------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ e ⟩ q ∋ `cast ±p [ ℰ ] ≤ ℰ′

  ≤cast : ∀ {ℰ ℰ′} {e : E ≤ᵉ E′}
      {p : A ≤ A′} {±q : A′ => B′} {r : A ≤ B′}
    → ≤commute p ±q r
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ e ⟩ p ∋ ℰ ≤ ℰ′
      -------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ e ⟩ r ∋ ℰ ≤ `cast ±q [ ℰ′ ]

  castᵉ≤ : ∀ {ℰ ℰ′} {a : A ≤ A′}
      {e : E ≤ᵉ E′} {±f : E =>ᵉ F} {f′ : F ≤ᵉ E′}
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ e ⟩ a ∋ ℰ ≤ ℰ′
      -----
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ f′ ⟩ a ∋ `castᵉ ±f [ ℰ ] ≤ ℰ′

  ≤castᵉ : ∀ {ℰ ℰ′} {a : A ≤ A′}
      {e : E ≤ᵉ E′} {±f : E′ =>ᵉ F′} {f′ : E ≤ᵉ F′}
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ e ⟩ a ∋ ℰ ≤ ℰ′
      -----
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ f′ ⟩ a ∋ ℰ ≤ `castᵉ ±f [ ℰ′ ]

  ″perform_[_]_ : ∀ {e} {ℰ ℰ′}
    → ((e∈E , e∈E′) : e ∈☆ E × e ∈☆ E′)
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id ∋ ℰ ≤ ℰ′
    → ∀ {A}
    → (eq : response e ≡ A)
      ---------------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ ⟨ E≤ ⟩ id
         ∋ ″perform e∈E [ ℰ ] eq
         ≤ ″perform e∈E′ [ ℰ′ ] eq

  ′handle_[_] : ∀ {Q₁ Q₁′ Q₂ Q₂′}
      {Q₁≤ : Q₁ ≤ᶜ Q₁′}
      {Q₂≤ : Q₂ ≤ᶜ Q₂′}
      {H H′} {ℰ ℰ′}
    → Γ≤ ⊢ H ≤ H′ ⦂ Q₁≤ ⇒ʰ Q₂≤
    → Γ≤ ⊢ P≤ ⇒ᶠ Q₁≤ ∋ ℰ ≤ ℰ′
      --------------------------
    → Γ≤ ⊢ P≤ ⇒ᶠ Q₂≤
         ∋ ′handle H [ ℰ ]
         ≤ ′handle H′ [ ℰ′ ]
```

\iffalse

TODO: three solutions to handle subtyping
- only judgement-level effect subtyping _⊑ᶜ_ = _⊑ᵉ_ × _≡_
- or treat all casts uniformly in cast≤ and ≤cast (requires indexing term precision by ≤⊑)
- or introduce subtyping square A ⊑ B -> A ≤ A′ → B ≤ B′ → A′ ⊑ B′ → Set

\fi

\iffalse

```
ren≤ᶠ : ∀ {ρ : Γ →ᴿ Δ} {ρ′ : Γ′ →ᴿ Δ′} {ℰ ℰ′}
  → Γ≤ →ᴿ Δ≤ ∋ ρ ≤ ρ′
  → Γ≤ ⊢ P≤ ⇒ᶠ Q≤ ∋ ℰ ≤ ℰ′
  → Δ≤ ⊢ P≤ ⇒ᶠ Q≤ ∋ renᶠ ρ ℰ ≤ renᶠ ρ′ ℰ′
ren≤ᶠ ρ≤ □ = □
ren≤ᶠ ρ≤ (by split≡ [ ℰ≤ ]· M≤) = by split≡ [ ren≤ᶠ ρ≤ ℰ≤ ]· ren≤ ρ≤ M≤
ren≤ᶠ ρ≤ (by split≡ , (v , v′ , V≤) ·[ ℰ≤ ]) = by split≡ , (ren-val _ v , ren-val _ v′ , ren≤ ρ≤ V≤) ·[ ren≤ᶠ ρ≤ ℰ≤ ]
ren≤ᶠ ρ≤ ([ ℰ≤ ]⦅ f ⦆ M≤) = [ ren≤ᶠ ρ≤ ℰ≤ ]⦅ f ⦆ ren≤ ρ≤ M≤
ren≤ᶠ ρ≤ ((v , v′ , V≤) ⦅ f ⦆[ ℰ≤ ]) = (ren-val _ v , ren-val _ v′ , ren≤ ρ≤ V≤) ⦅ f ⦆[ ren≤ᶠ ρ≤ ℰ≤ ]
ren≤ᶠ ρ≤ ([ ℰ≤ ]⇑ g) = [ ren≤ᶠ ρ≤ ℰ≤ ]⇑ g
ren≤ᶠ ρ≤ (≤⇑ ℰ≤) = ≤⇑ (ren≤ᶠ ρ≤ ℰ≤)
ren≤ᶠ ρ≤ (cast≤ comm ℰ≤) = cast≤ comm (ren≤ᶠ ρ≤ ℰ≤)
ren≤ᶠ ρ≤ (≤cast comm ℰ≤) = ≤cast comm (ren≤ᶠ ρ≤ ℰ≤)
ren≤ᶠ ρ≤ (castᵉ≤ ℰ≤) = castᵉ≤ (ren≤ᶠ ρ≤ ℰ≤)
ren≤ᶠ ρ≤ (≤castᵉ ℰ≤) = ≤castᵉ (ren≤ᶠ ρ≤ ℰ≤)
ren≤ᶠ ρ≤ (″perform (e∈E , e∈E′) [ ℰ≤ ] eq) = ″perform (e∈E , e∈E′) [ ren≤ᶠ ρ≤ ℰ≤ ] eq
ren≤ᶠ ρ≤ (′handle H≤ [ ℰ≤ ]) = ′handle (ren≤ʰ ρ≤ H≤) [ ren≤ᶠ ρ≤ ℰ≤ ]

lift≤ᶠ : ∀ {ℰ ℰ′}
  → Γ≤ ⊢ P≤ ⇒ᶠ Q≤ ∋ ℰ ≤ ℰ′
  → Γ≤ ▷ A≤ ⊢ P≤ ⇒ᶠ Q≤ ∋ liftᶠ ℰ ≤ liftᶠ ℰ′
lift≤ᶠ = ren≤ᶠ S≤S

⟦⟧≤⟦⟧ : ∀ {ℰ ℰ′ M M′}
  → Γ≤ ⊢ P≤ ⇒ᶠ Q≤ ∋ ℰ ≤ ℰ′
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ P≤
  → Γ≤ ⊢ ℰ ⟦ M ⟧ ≤ᴹ ℰ′ ⟦ M′ ⟧ ⦂ Q≤
⟦⟧≤⟦⟧ □ M≤ = M≤
⟦⟧≤⟦⟧ (by split≡ [ ℰ≤ ]· N≤) M≤ = ·≤· split≡ (⟦⟧≤⟦⟧ ℰ≤ M≤) N≤
⟦⟧≤⟦⟧ (by split≡ , (v , v′ , V≤) ·[ ℰ≤ ]) M≤ = ·≤· split≡ V≤ (⟦⟧≤⟦⟧ ℰ≤ M≤)
⟦⟧≤⟦⟧ ([ ℰ≤ ]⦅ f ⦆ N≤) M≤ = ⦅⦆≤⦅⦆ f (⟦⟧≤⟦⟧ ℰ≤ M≤) N≤
⟦⟧≤⟦⟧ ((v , v′ , V≤) ⦅ f ⦆[ ℰ≤ ]) M≤ = ⦅⦆≤⦅⦆ f V≤ (⟦⟧≤⟦⟧ ℰ≤ M≤)
⟦⟧≤⟦⟧ ([ ℰ≤ ]⇑ g) M≤ = ⇑≤⇑ g (⟦⟧≤⟦⟧ ℰ≤ M≤)
⟦⟧≤⟦⟧ (≤⇑ ℰ≤) M≤ = ≤⇑ _ (⟦⟧≤⟦⟧ ℰ≤ M≤)
⟦⟧≤⟦⟧ (cast≤ comm ℰ≤) M≤ = cast≤ comm (⟦⟧≤⟦⟧ ℰ≤ M≤)
⟦⟧≤⟦⟧ (≤cast comm ℰ≤) M≤ = ≤cast comm (⟦⟧≤⟦⟧ ℰ≤ M≤)
⟦⟧≤⟦⟧ (castᵉ≤ ℰ≤) M≤ = castᵉ≤ (⟦⟧≤⟦⟧ ℰ≤ M≤)
⟦⟧≤⟦⟧ (≤castᵉ ℰ≤) M≤ = ≤castᵉ (⟦⟧≤⟦⟧ ℰ≤ M≤)
⟦⟧≤⟦⟧ (″perform (e∈E , e∈E′) [ ℰ≤ ] eq) M≤ = perform≤perform (⟦⟧≤⟦⟧ ℰ≤ M≤)
⟦⟧≤⟦⟧ (′handle H≤ [ ℰ≤ ]) M≤ = handle≤handle H≤ (⟦⟧≤⟦⟧ ℰ≤ M≤)
```
\fi

## Precision on values

Values are a subset of terms, so we don't need to define a separate relation for them.
The following lemmas state that value precision is preserved by generalization (`gvalue`).
```
gvalue≤gvalue :
    {V : Γ ⊢ ⟨ E ⟩ A}
    {V′ : Γ′ ⊢ ⟨ E′ ⟩ A′}
  → (v  : Value V)
  → (v′ : Value V′)
  → Γ≤ ⊢ V ≤ᴹ V′ ⦂ ⟨ E≤ ⟩ A≤
  → ∀ {F F′} {F≤ : F ≤ᵉ F′}
    --------------------------------------
  → Γ≤ ⊢ gvalue v ≤ᴹ gvalue v′ ⦂ ⟨ F≤ ⟩ A≤
```

\iffalse
```
gvalue≤gvalue ($ _) ($ _) ($≤$ κ) = $≤$ κ
gvalue≤gvalue (v ⇑ _) (v′ ⇑ _) (⇑≤⇑ g V≤) = ⇑≤⇑ g (gvalue≤gvalue v v′ V≤)
gvalue≤gvalue v (v′ ⇑ _) (≤⇑ g V≤) = ≤⇑ g (gvalue≤gvalue v v′ V≤)
gvalue≤gvalue (ƛ _) (ƛ _) (ƛ≤ƛ split≡ N≤N′) = ƛ≤ƛ split≡ N≤N′
gvalue≤gvalue (ƛ _) (ƛ _) (wrap≤ i e ƛN≤ƛN′) = wrap≤ i e ƛN≤ƛN′
gvalue≤gvalue (ƛ _) (ƛ _) (≤wrap i e ƛN≤ƛN′) = ≤wrap i e ƛN≤ƛN′
```
\fi

\iffalse
```
gValue : {V : Γ ⊢ ⟨ E ⟩ A}
       → (v : Value V) → ∀ {F}
       → Value (gvalue v {F = F})
gValue (ƛ N) = ƛ N
gValue ($ κ) = $ κ
gValue (v ⇑ g) = gValue v ⇑ g
```

```
≤gvalue :
    {V : Γ ⊢ ⟨ E ⟩ A}
    {V′ : Γ′ ⊢ ⟨ E′ ⟩ A′}
  → (v  : Value V)
  → (v′ : Value V′)
  → Γ≤ ⊢ V ≤ᴹ V′ ⦂ ⟨ E≤ ⟩ A≤
  → ∀ {F′} {F≤ : E ≤ᵉ F′}
  → Γ≤ ⊢ V ≤ᴹ gvalue v′ ⦂ ⟨ F≤ ⟩ A≤
```
\fi

\iffalse
```
≤gvalue ($ _) ($ _) ($≤$ κ) = $≤$ κ
≤gvalue (v ⇑ _) (v′ ⇑ _) (⇑≤⇑ g V≤) = ⇑≤⇑ g (≤gvalue v v′ V≤)
≤gvalue v (v′ ⇑ _) (≤⇑ g V≤) = ≤⇑ g (≤gvalue v v′ V≤)
≤gvalue (ƛ _) (ƛ _) (ƛ≤ƛ split≡ N≤N′) = ƛ≤ƛ split≡ N≤N′
≤gvalue (ƛ _) (ƛ _) (wrap≤ i e ƛN≤ƛN′) = wrap≤ i e ƛN≤ƛN′
≤gvalue (ƛ _) (ƛ _) (≤wrap i e ƛN≤ƛN′) = ≤wrap i e ƛN≤ƛN′
```
\fi

\iffalse
```
gvalue≤ :
    {V : Γ ⊢ ⟨ E ⟩ A}
    {V′ : Γ′ ⊢ ⟨ E′ ⟩ A′}
  → (v : Value V)
  → (v′ : Value V′)
  → Γ≤ ⊢ V ≤ᴹ V′ ⦂ ⟨ E≤ ⟩ A≤
  → ∀ {F} {F≤ : F ≤ᵉ E′}
  → Γ≤ ⊢ gvalue v ≤ᴹ V′ ⦂ ⟨ F≤ ⟩ A≤
```
\fi

\iffalse
```
gvalue≤ ($ _) ($ _) ($≤$ κ) = $≤$ κ
gvalue≤ (v ⇑ _) (v′ ⇑ _) (⇑≤⇑ g V≤) = ⇑≤⇑ g (gvalue≤ v v′ V≤)
gvalue≤ v (v′ ⇑ _) (≤⇑ g V≤) = ≤⇑ g (gvalue≤ v v′ V≤)
gvalue≤ (ƛ _) (ƛ _) (ƛ≤ƛ split≡ N≤N′) = ƛ≤ƛ split≡ N≤N′
gvalue≤ (ƛ _) (ƛ _) (wrap≤ i e ƛN≤ƛN′) = wrap≤ i e ƛN≤ƛN′
gvalue≤ (ƛ _) (ƛ _) (≤wrap i e ƛN≤ƛN′) = ≤wrap i e ƛN≤ƛN′
```
\fi
