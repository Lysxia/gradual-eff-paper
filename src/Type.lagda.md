# Types and effects

We define types, effects, and the *precision* relation on types.

\iffalse
```
module Type where

open import Utils

import Data.List.Relation.Unary.Any.Properties as Any
```
\fi

The module `Utils` reexports the standard library and exports some additional
general lemmas. It is in the \Cref{sec:appendix}.

## Base types

Base types are primitive data types such as numbers and booleans.
```
data Base : Set where
  ′ℕ : Base
  ′𝔹 : Base
  ′𝕌 : Base
```

The `rep` function interprets base types into Agda types.
```
rep : Base → Set
rep ′ℕ  =  ℕ
rep ′𝔹  =  𝔹
rep ′𝕌  =  ⊤
```

\iffalse

Decision procedure for equality of base types.
```
_≡$?_ : (ι ι′ : Base) → Dec (ι ≡ ι′)
```

```
′ℕ  ≡$? ′ℕ  =  yes refl
′ℕ  ≡$? ′𝔹  =  no λ()
′ℕ  ≡$? ′𝕌  =  no λ()
′𝔹  ≡$? ′ℕ  =  no λ()
′𝔹  ≡$? ′𝔹  =  yes refl
′𝔹  ≡$? ′𝕌  =  no λ()
′𝕌  ≡$? ′ℕ  =  no λ()
′𝕌  ≡$? ′𝔹  =  no λ()
′𝕌  ≡$? ′𝕌  =  yes refl
```

\fi

## Effects

Algebraic effects are names that a program may call, submitting
a request with some arguments, expecting some result in response.

We represent those names simply as strings.
```
Op : Set
Op = String
```

A type-and-effect system keeps track of the operations that a computation may
perform. A \emph{gradual effect} `E : Effect` may be either static or dynamic.
A static effect is a list of operations that a computation may perform.
The dynamic effect `☆` allows a computation to perform any operations.
```
StaticEffect : Set
StaticEffect = List Op
```

\iffalse
```
infix 7 ¡_
```
\fi

```
data Effect : Set where
  ¡_ : StaticEffect → Effect
  ☆ : Effect
```

Pattern synonym for the empty effect (a computation which calls no operations).
```
pattern ε = ¡ []
```

\emph{Consistent membership} lifts the membership relation `_∈_` from lists (static
effects) to gradual effects.
The dynamic effect statically accepts any effect `e` as a member.

\lyx{Compare with~\cite{sekiyama2019gradual,schwerter2016gradual}}
\iffalse
```
infix 4 _∈☆_
```
\fi

```
data _∈☆_ (e : Op) : Effect → Set where
  ¡_ : ∀ {E} → e ∈ E → e ∈☆ ¡ E
  ☆  : e ∈☆ ☆
```

List concatenation `_++_` is similarly lifted to gradual effects:
extending the dynamic effect yields back the dynamic effect.
```
_++☆_ : List Op → Effect → Effect
E ++☆ ☆ = ☆
E ++☆ (¡ F) = ¡ (E ++ F)
```

\iffalse

Decision procedure for `_∈☆_`.
```
_∈☆?_ : ∀ e E → Dec (e ∈☆ E)
e ∈☆? ☆ = yes ☆
e ∈☆? (¡ E) with e ∈? E
... | yes e∈E = yes (¡ e∈E)
... | no ¬e∈E = no λ{ (¡ e∈E) → ¬e∈E e∈E }
```

Consistent membership is preserved by concatenation.
```
∈☆-++☆ʳ : ∀ {e Eh E} → e ∈☆ E → e ∈☆ (Eh ++☆ E)
∈☆-++☆ʳ {Eh = Eh} (¡ e) = ¡ (Any.++⁺ʳ Eh e)
∈☆-++☆ʳ ☆ = ☆
```

Inversion lemma for consistent membership.
```
∈☆-++☆⁻ : ∀ {e Eh E} → e ∈☆ (Eh ++☆ E)
  → e ∈ Eh ⊎ e ∈☆ E
∈☆-++☆⁻ {E = ☆} _ = inj₂ ☆
∈☆-++☆⁻ {Eh = Eh} {E = ¡ _} (¡ e∈++)
    with Any.++⁻ Eh e∈++
... | inj₁ e∈Eh = inj₁ e∈Eh
... | inj₂ e∈E = inj₂ (¡ e∈E)
```
\fi

## Types

\iffalse
```
infixr 7 _⇒_
infix  8 $_
infix 7 ⟨_⟩_
```
\fi

We distinguish computations from the values they return, assigning them different notions
of types. Computation types `CType` \lyx{or CType?} are pairs of effects `Effect` and value types `Type`.
Computation types and value types are defined mutually recursively, so we declare both of their
type signatures before giving their definitions.
```
record CType : Set
data Type : Set
```

A value type can be the dynamic type `★` for values whose type will be known at run time.
The base type `$_` is for primitives. And the function type has a domain which is a value type
and a codomain which is a computation type: when a function is applied, it may perform effects.
```
data Type where
  ★ : Type
  $_ : (ι : Base) → Type
  _⇒_ : (A : Type) → (P : CType) → Type
```

Computation types are pairs of an effect and a value type,
respectively describing the operations that a computation may perform,
and the values that it may return.

```
record CType where
  inductive
  constructor ⟨_⟩_
  field
    effects : Effect
    returns : Type
```

\iffalse
```
private variable
  A A′ A″ B B′ B″ C D : Type
  P P′ P″ Q : CType
  E F : Effect
```
\fi

\iffalse

(TODO) the base type ′𝔹 doesn't have eliminators ("if") yet. In the meantime here's Church encoded booleans
```
-- Church booleans
pattern 𝟚 = ★ ⇒ ⟨ ☆ ⟩ ★ ⇒ ⟨ ☆ ⟩ ★
```

\fi

Having defined types, we can assign signatures to operations, which are their
input and output types, also called requests and responses.
```
Op-sig : Op → Type × Type
Op-sig "get"     =  ($ ′𝕌 , $ ′ℕ)
Op-sig "put"     =  ($ ′ℕ , $ ′𝕌)
Op-sig "choose"  =  ($ ′𝕌 , 𝟚)     -- TODO: conditionals (eliminate bool)
Op-sig "fail"    =  ($ ′𝕌 , $ ′𝕌)  -- TODO: empty type
Op-sig _         =  (★ , ★)

request : Op → Type
request e = proj₁ (Op-sig e)

response : Op → Type
response e = proj₂ (Op-sig e)
```

\iffalse

Decision procedure for equality of types.
```
infix 4 _≡ᵉ?_ _≡ᶜ?_ _≡?_

_≡ᵉ?_ : (E F : Effect) → Dec (E ≡ F)
_≡ᶜ?_ : (P Q : CType) → Dec (P ≡ Q)
_≡?_ : (A B : Type) → Dec (A ≡ B)
```
\fi

\iffalse
```
☆ ≡ᵉ? ☆ = yes refl
¡ E ≡ᵉ? ¡ F with E ≟ F
... | yes refl = yes refl
... | no ¬≡ = no λ{ refl → ¬≡ refl }
¡ _ ≡ᵉ? ☆ = no λ()
☆ ≡ᵉ? ¡ _ = no λ()

★       ≡? ★                                   =  yes refl
★       ≡? ($ _)                               =  no (λ ())
★       ≡? (_ ⇒ _)                             =  no (λ ())
($ _)   ≡? ★                                   =  no (λ ())
($ ι)   ≡? ($ κ)     with ι ≡$? κ
...                     | yes refl             =  yes refl
...                     | no  ι≢κ              =  no  (λ{refl → ι≢κ refl})
($ _)   ≡? (_ ⇒ _)                             =  no  (λ ())
(_ ⇒ _) ≡? ★                                   =  no  (λ ())
(_ ⇒ _) ≡? ($ _)                               =  no  (λ ())
(A ⇒ B) ≡? (A′ ⇒ B′) with A ≡? A′ ×-dec B ≡ᶜ? B′
...                     | yes (refl , refl)    =  yes refl
...                     | no  ¬A≡A′×B≡B′       =  no  (λ{refl → ¬A≡A′×B≡B′ (refl , refl)})

⟨ E ⟩ A ≡ᶜ? ⟨ F ⟩ B with E ≡ᵉ? F ×-dec A ≡? B
... | yes (refl , refl) = yes refl
... | no ¬≡×≡ = no λ{ refl → ¬≡×≡ (refl , refl) }
```
\fi

Gradual types let us control how much information about the program's
behavior we want to keep track of at compile time or at run time.
There is an ordering of types, called *precision*, with `★` at the top
and completely static types at the bottom, with no occurrences of `★`.
Intuitively, more precise types provide more static information,
while less precise types give more flexibility in exchange for more
run-time checks. We define precision in the rest of this section.

## Precision

### Ground types

One early dimension to consider in designing a gradual type system is whether
to compare types at run time *deeply* or *shallowly*. Deep type comparisons
are known to break the gradual guarantee~\citep{boyland2014problem}, so we will go with shallow type
comparisons. *Ground types* are those that reflect exactly the information learned
from such a shallow comparison. We only look at the first type constructor
of a type, so the type is either a base type `$_` or a function type `_⇒_`,
and in the latter case we don't learn anything about the domain or codomain,
so the most precise type describing what we know is `★ ⇒ ⟨ ☆ ⟩ ★`.
```
data Ground : Type → Set where
  $_
    :  (ι : Base)
       ------------
    →  Ground ($ ι)

  ★⇒★
    :  --------------
       Ground (★ ⇒ ⟨ ☆ ⟩ ★)
```

\iffalse
Extract type from evidence that it is ground
```
ground : ∀ {G} → (g : Ground G) → Type
ground {G = G} g  =  G
```

Evidence for a ground type is unique.
```
uniqueG : ∀ {G} → (g h : Ground G) → g ≡ h
uniqueG ($ ι) ($ .ι) = refl
uniqueG ★⇒★   ★⇒★    = refl
```

Star is not ground
```
G≢★ : ∀ {G} → (g : Ground G) → G ≢ ★
G≢★ () refl
```
\fi

### The precision relation

\iffalse
```
infix 4 _≤_ _≤ᵉ_ _≤ᶜ_
infixl 5 _⇑_
```
\fi

Precision orders types by how much static information they
tell us about their values.

The dynamic effect `☆` is less precise than any static effect `¡ E`.
\lyx{If we really wanted to treat lists as set, this should also allow reordering.}
```
data _≤ᵉ_ : (_ _ : Effect) → Set where
  id : ∀ {E} → E ≤ᵉ E
  ¡≤☆ : ∀ {E} → ¡ E ≤ᵉ ☆
```

`☆` is the least precise element in `Effect`.
```
≤☆ : ∀ {E} → E ≤ᵉ ☆
≤☆ {☆} = id
≤☆ {¡ _} = ¡≤☆
```

Since computation types and value types are mutually recursive, their
respective precision relations are also mutually recursive. We declare
the signature of one before defining the other.
```
record _≤ᶜ_ (_ _ : CType) : Set
```

A staple of gradual typing is that the function type is covariant in both domain and codomain
with respect to precision.
```
data _≤_ : Type → Type → Set where

  _⇒_ : ∀ {A P A′ P′}
    → A ≤ A′
    → P ≤ᶜ P′
      ---------------
    → A ⇒ P ≤ A′ ⇒ P′
```

The dynamic type `★` is less precise than all types. However, following the principle
that run-time type comparisons will be shallow, when we compare an arbitrary type `A` with `★`,
we look at the first constructor, represented by a ground type `G`, and further comparisons
are done by comparing the components of `A` with those of `G` (which are necessarily `★` or `☆`).
```
  _⇑_ : ∀ {A G}
    → A ≤ G
    → Ground G
      -----
    → A ≤ ★
```

The reflexivity of `_≤_` includes the fact that base types `$_` are related
only to themselves. In fact, we could ensure that `A ≤ B` is a singleton
by restricting the `id` rule to base types. Although this would simplify some proofs,
we view this uniqueness as an artifact of the simple type system being formalized.
It is generally useful for coercions (which we will represent as proofs of precision)
to have non-trivial structure, for purposes both practical---an identity
coercion which can be immediately discarded enables better performance---and
theoretical---with polymorphism, derivations of precisions tend to not be unique.
```
  id : ∀ {A}
      -----
    → A ≤ A
```

Precision between computation types composes precision between their effect and
value components.
```
record _≤ᶜ_ P Q where
  inductive
  constructor ⟨_⟩_
  field
    effects : CType.effects P ≤ᵉ CType.effects Q
    returns : CType.returns P ≤  CType.returns Q
```

Domain and codomain of function precision.

```
split⇒ : ∀ {A A′ E E′ B B′} (p : A ⇒ ⟨ E ⟩ B ≤ A′ ⇒ ⟨ E′ ⟩ B′) → (A ≤ A′) × (E ≤ᵉ E′) × (B ≤ B′)
split⇒ id = id , id , id
split⇒ (a ⇒ ⟨ e ⟩ b) = a , e , b
```

```
dom : ∀ {A B A′ B′} → A ⇒ B ≤ A′ ⇒ B′ → A ≤ A′
dom a = proj₁ (split⇒ a)

cod : ∀ {A B E A′ B′ E′} → A ⇒ ⟨ E ⟩ B ≤ A′ ⇒ ⟨ E′ ⟩ B′ → B ≤ B′
cod a = proj₂ (proj₂ (split⇒ a))

eff : ∀ {A B E A′ B′ E′} → A ⇒ ⟨ E ⟩ B ≤ A′ ⇒ ⟨ E′ ⟩ B′ → E ≤ᵉ E′
eff a = proj₁ (proj₂ (split⇒ a))
```

The use of these two functions is reminiscent of some gradually-typed
source languages, where one defines

```txt
    dom ★        =  ★
    dom (A ⇒ B)  =  A

    cod ★        =  ★
    cod (A ⇒ B)  =  B
```

and has a typing rule resembling

```txt
    Γ ⊢ L : A
    Γ ⊢ M : dom A
    ------------------
    Γ ⊢ L · M : cod A
```

Our `dom` and `cod` will play a similar role when we define the
precedence rules for abstraction and application.

\iffalse
Lemma. Every ground type is more precise than `★`.
```
G≤★ : ∀ {G} → Ground G → G ≤ ★
G≤★ ($ ι)  =  id ⇑ $ ι
G≤★ ★⇒★    =  (id ⇒ ⟨ id ⟩ id) ⇑ ★⇒★
```

Lemma. `★` is not more precise than any ground type.
```
¬★≤G : ∀ {G} → Ground G → ¬ (★ ≤ G)
¬★≤G ($ ι) ()
¬★≤G ★⇒★   ()
```

Lemma. `★` is least precise.
```
★≤ : ∀ {A} → ★ ≤ A → A ≡ ★
★≤ {★} p  =  refl
★≤ {$ ι} ()
★≤ {A ⇒ B} ()
```

Lemma. Every effect is more precise than `☆`.
```
E≤☆ : ∀ {E} → E ≤ᵉ ☆
E≤☆ {☆} = id
E≤☆ {¡ E} = ¡≤☆
```

Lemma. Every type is more precise than `★`. (Not true in general.)\lyx{?}
```
A≤★ : ∀ {A} → A ≤ ★
A≤★ {★}      =  id
A≤★ {$ ι}    =  id ⇑ $ ι
A≤★ {A ⇒ B}  =  (A≤★ ⇒ ⟨ E≤☆ ⟩ A≤★) ⇑ ★⇒★
```

Lemma. Every type is either `★` or more precise than a ground type. (Not true in general.)
```
★⊎G : (A ≡ ★) ⊎ ∃[ G ](Ground G × A ≤ G)
★⊎G {★}      =  inj₁ refl
★⊎G {$ ι}    =  inj₂ ($ ι , $ ι , id)
★⊎G {A ⇒ B}  =  inj₂
  (★ ⇒ ⟨ ☆ ⟩ ★ , ★⇒★ , A≤★ ⇒ ⟨ E≤☆ ⟩ A≤★)
```

Lemma. If a type is more precise than a ground type, it is not `★`.
```
≢★ : ∀ {A G} → Ground G → A ≤ G → A ≢ ★
≢★ g A≤G A≡★ rewrite A≡★ = ¬★≤G g A≤G
```

Lemma. `_≤_` is transitive. This lemma gives the composition in the category of types and precision.
```
_⨟ᵉ_ : ∀ {A B C} → A ≤ᵉ B → B ≤ᵉ C → A ≤ᵉ C
d ⨟ᵉ id = d
id ⨟ᵉ ¡≤☆ = ¡≤☆

_⨟ᶜ_ : ∀ {A B C} → A ≤ᶜ B → B ≤ᶜ C → A ≤ᶜ C
_⨟_ : ∀ {A B C} → A ≤ B → B ≤ C → A ≤ C
p ⨟ id                     =  p
p ⨟ (q ⇑ g)                =  (p ⨟ q) ⇑ g
_⨟_ {A = _ ⇒ _} p (q ⇒ r)  =  (dom p ⨟ q) ⇒ ((⟨ eff p ⟩ cod p) ⨟ᶜ r)

(⟨ d ⟩ p) ⨟ᶜ (⟨ e ⟩ q) = ⟨ d ⨟ᵉ e ⟩ (p ⨟ q)
```

Lemmas. Left and right identity.
```
left-idᵉ : (p : E ≤ᵉ F) → id ⨟ᵉ p ≡ p
left-idᶜ : (p : P ≤ᶜ Q) → (⟨ id ⟩ id) ⨟ᶜ p ≡ p
left-id  : (p : A ≤ B) → id ⨟ p ≡ p
```
\fi

\iffalse
```
left-idᵉ id = refl
left-idᵉ ¡≤☆ = refl

left-id id                             =  refl
left-id (p ⇑ g) rewrite left-id p      =  refl
left-id (p ⇒ q) rewrite left-id p
                      | left-idᶜ q     =  refl

left-idᶜ (⟨ d ⟩ p) rewrite left-idᵉ d
                         | left-id p   = refl
```
\fi

\iffalse
```
right-id : ∀ {A B} → (p : A ≤ B) → p ⨟ id ≡ p
right-id p  =  refl
```
\fi

\iffalse
```
module _ where
  private variable
    G H : Effect
    R S : CType
```
\fi

\iffalse
Lemma. Associativity.
```
  assocᵉ : ∀ (p : E ≤ᵉ F) (q : F ≤ᵉ G) (r : G ≤ᵉ H)
    → (p ⨟ᵉ q) ⨟ᵉ r ≡ p ⨟ᵉ (q ⨟ᵉ r)
  assocᵉ p q id = refl
  assocᵉ id id ¡≤☆ = refl

  assocᶜ : ∀ (p : P ≤ᶜ Q) (q : Q ≤ᶜ R) (r : R ≤ᶜ S)
    → (p ⨟ᶜ q) ⨟ᶜ r ≡ p ⨟ᶜ (q ⨟ᶜ r)

  assoc : ∀ (p : A ≤ B) (q : B ≤ C) (r : C ≤ D)
    → (p ⨟ q) ⨟ r ≡ p ⨟ (q ⨟ r)
  assoc p q id                                     = refl
  assoc p id r rewrite left-id r                   = refl
  assoc id q r rewrite left-id q | left-id (q ⨟ r) = refl
  assoc p q (r ⇑ g) rewrite assoc p q r            = refl
  assoc (p ⇒ p′) (q ⇒ q′) (r ⇒ r′) rewrite assoc p q r | assocᶜ p′ q′ r′   =  refl

  assocᶜ (⟨ d ⟩ p) (⟨ e ⟩ q) (⟨ f ⟩ r)
    rewrite assocᵉ d e f | assoc p q r = refl
```

Lemma. `dom` and `cod` are functors.

```
dom-⨟ :
       (p : A ⇒ P ≤ A′ ⇒ P′)
    →  (q : A′ ⇒ P′ ≤  A″ ⇒ P″)
    →  dom p ⨟ dom q ≡ dom (p ⨟ q)
dom-⨟ id id = refl
dom-⨟ id (_ ⇒ _) = refl
dom-⨟ (_ ⇒ _) id = refl
dom-⨟ (_ ⇒ _) (_ ⇒ _) = refl

cod-⨟ :
       (p : A ⇒ P ≤ A′ ⇒ P′)
    →  (q : A′ ⇒ P′ ≤  A″ ⇒ P″)
    →  cod p ⨟ cod q ≡ cod (p ⨟ q)
cod-⨟ id id = refl
cod-⨟ id (_ ⇒ _) = refl
cod-⨟ (_ ⇒ _) id = refl
cod-⨟ (_ ⇒ _) (_ ⇒ _) = refl
```

Lemma. If `p : ★ ≤ ★` then `p ≡ id`.
```
★≤★→≡id : ∀ (p : ★ ≤ ★) → p ≡ id
★≤★→≡id id       =  refl
★≤★→≡id (p ⇑ g)  =  ⊥-elim (¬★≤G g p)
```

Lemma. Consistent membership is preserved by decreases in precision.
```
∈-≤ : ∀ {E F e} → E ≤ᵉ F → e ∈☆ E → e ∈☆ F
∈-≤ id e∈E = e∈E
∈-≤ ¡≤☆ _ = ☆
```
\fi

\iffalse
## Subtyping

```
infix 4 _⊑ᵉ_ _⊑ᶜ_ _⊑_
```

Static effects have a natural notion of subtyping:
an effect `E` is a subeffect of `F` if `E` is a subset of `F`.
We lift this notion to gradual effects by treating the dynamic
effect `☆` as only a subeffect of itself.
[TODO citations, New Perspective] We thus treat subtyping orthogonally to
gradual typing.

```
data _⊑ᵉ_ : Effect → Effect → Set where
  ☆ : ☆ ⊑ᵉ ☆
  ¡_ : ∀ {E F} → E ⊆ F → ¡ E ⊑ᵉ ¡ F
```

Lemma. The subeffect relation is reflexive.
```
⊑ᵉ-refl : ∀ {E} → E ⊑ᵉ E
⊑ᵉ-refl {☆} = ☆
⊑ᵉ-refl {¡ _} = ¡ ⊆-refl
```

We obtain a subtyping relation between types, again as two mutually recursive
relations between value types and computation types.

```
data _⊑_ : Type → Type → Set
record _⊑ᶜ_ (P Q : CType) : Set
```

Subtyping is contravariant in the domain of a function type,
unlike precision.

```
data _⊑_ where
  id : ∀ {E} → E ⊑ E
  _⇒_ :
       A′ ⊑ A
    →  P ⊑ᶜ P′
       -------------------
    →  (A ⇒ P) ⊑ (A′ ⇒ P′)
```

We use the subeffect relation above to define subtyping
between computation types.

```
record _⊑ᶜ_ P Q where
  inductive
  constructor ⟨_⟩_
  field
    effects : CType.effects P ⊑ᵉ CType.effects Q
    returns : CType.returns P ⊑  CType.returns Q
```

```
⊑ᶜ-refl : ∀ {P} → P ⊑ᶜ P
⊑ᶜ-refl = ⟨ ⊑ᵉ-refl ⟩ id
```
\fi

## Casts

`\begin{AgdaAlign}`{=tex}
```
infix  6 _=>_ _=>ᶜ_ _=>ᵉ_
infix  4 +_ -_
```

We define notions of casts for the different precision relations
`_≤_`, `_≤ᶜ_`, `_≤ᵉ_` uniformly with the `Cast` combinator.
\lyx{Ignore subtyping}

```
data Cast {S : Set}
  (_<_ _⊏_ : S → S → Set) (A B : S) : Set where
```

There are three kinds of casts. Upcasts reduce precision, \eg{} casting from `$ ι` to `★`,
```
  +_  : A < B
        ----------------
      → Cast _<_ _⊏_ A B
```

Downcasts increase precision.
```
  -_  : B < A
        ----------------
      → Cast _<_ _⊏_ A B
```
`\end{AgdaAlign}`{=tex}

The types of casts for value types, computation types, and effects
are obtaines by applying `Cast` to their respective precision and subtyping relations.

```
_=>_ : Type → Type → Set
_=>_ = Cast _≤_ _⊑_

_=>ᶜ_ : CType → CType → Set
_=>ᶜ_ = Cast _≤ᶜ_ _⊑ᶜ_

_=>ᵉ_ : Effect → Effect → Set
_=>ᵉ_ = Cast _≤ᵉ_ _⊑ᵉ_
```

\iffalse
The empty list, viewed as a set, is a subset of any other list.
```
[]⊆ : ∀ {A : Set} {xs : List A} → [] ⊆ xs
[]⊆ ()
```

Projections of computation casts.
```
=>ᶜ-effects : (±p : ⟨ E ⟩ A =>ᶜ ⟨ F ⟩ B)
  → E =>ᵉ F
=>ᶜ-effects (+ ⟨ p ⟩ _) = + p
=>ᶜ-effects (- ⟨ p ⟩ _) = - p

=>ᶜ-returns : (±p : ⟨ E ⟩ A =>ᶜ ⟨ F ⟩ B)
  → A => B
=>ᶜ-returns (+ ⟨ _ ⟩ q) = + q
=>ᶜ-returns (- ⟨ _ ⟩ q) = - q
```

Pure casts: the identity on effects.
```
pure± : A => B  →  ⟨ E ⟩ A =>ᶜ ⟨ E ⟩ B
pure± (+ A≤) = + ⟨ id ⟩ A≤
pure± (- A≤) = - ⟨ id ⟩ A≤
```
\fi
