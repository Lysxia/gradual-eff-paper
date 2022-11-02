# Types and effects

We define types, effects, and the *precision* relation on types.

```
module Type where

open import Utils
```

The module `Utils` reexports the standard library and exports some additional
general lemmas. It is in the \Cref{sec:appendix}.

## Base types

Base types are primitive data types such as numbers and booleans.
```
data Base : Set where
  ′ℕ : Base
  ′𝔹 : Base
```

The `rep` function interprets base types into Agda types.
```
rep : Base → Set
rep ′ℕ  =  ℕ
rep ′𝔹  =  𝔹
```

Decision procedure for equality of base types.
```
_≡$?_ : (ι : Base) → (ι′ : Base) → Dec (ι ≡ ι′)
′ℕ  ≡$? ′ℕ  =  yes refl
′ℕ  ≡$? ′𝔹  =  no (λ ())
′𝔹  ≡$? ′ℕ  =  no (λ ())
′𝔹  ≡$? ′𝔹  =  yes refl
```

## Effects

Algebraic effects are names that a program may call, submitting
a request with some arguments, expecting some result in response.

We represent those names simply as strings.
```
𝔼 : Set
𝔼 = String
```

A type-and-effect system keeps track of the names that a computation may
call. We represent such a set of names concretely as a list.
In our gradual system, effects may also be checked dynamically,
assigning them the dynamic effect `¿`.

TODO: fix the naming. What to call `e : 𝔼` (names?), `es : List 𝔼`, and `E : Effs`?
Also `Effs` is a terrible name.
```
infix 7 ¡_

data Effs : Set where
  ¡_ : List 𝔼 → Effs
  ¿ : Effs
```

Pattern synonym for the empty effect (a computation which calls no names).
```
pattern ε = ¡ []
```

Consistent membership lifts the membership relation `_∈_` from lists (static
effect rows) to gradual effect rows.
The dynamic effect row statically accepts any effect `e` as a member.

TODO: Compare with~\cite{sekiyama2019gradual}
```
infix 4 _∈¿_

data _∈¿_ (e : 𝔼) : Effs → Set where
  ¡_ : ∀ {E} → e ∈ E → e ∈¿ ¡ E
  ¿  : e ∈¿ ¿

_++¿_ : List 𝔼 → Effs → Effs
E ++¿ ¿ = ¿
E ++¿ (¡ F) = ¡ (E ++ F)
```

## Types

```
infixr 7 _⇒_
infix  8 $_
infix 7 ⟨_⟩_

record Typeᶜ : Set

data Type : Set where
  ★ : Type
  $_ : (ι : Base) → Type
  _⇒_ : (A : Type) → (P : Typeᶜ) → Type

record Typeᶜ where
  inductive
  constructor ⟨_⟩_
  field
    effects : Effs
    returns : Type

𝔼-sig : 𝔼 → Type × Type
𝔼-sig "get" = ($ ′𝔹 , $ ′ℕ)
𝔼-sig "put" = ($ ′ℕ , $ ′𝔹)
𝔼-sig _ = (★ , ★)

request : 𝔼 → Type
request e = proj₁ (𝔼-sig e)

response : 𝔼 → Type
response e = proj₂ (𝔼-sig e)
```

Decision procedure for equality of types.
```
infix 4 _≡ᵉ?_ _≡ᶜ?_ _≡?_

_≡ᵉ?_ : Decidable {A = Effs} _≡_
¿ ≡ᵉ? ¿ = yes refl
¡ E ≡ᵉ? ¡ F with E ≟ F
... | yes refl = yes refl
... | no ¬≡ = no λ{ refl → ¬≡ refl }
¡ _ ≡ᵉ? ¿ = no λ()
¿ ≡ᵉ? ¡ _ = no λ()

_≡ᶜ?_ : (P Q : Typeᶜ) → Dec (P ≡ Q)

_≡?_ : (A : Type) → (B : Type) → Dec (A ≡ B)
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

private
  variable
    A A′ B G : Type
    P P′ Q Q′ : Typeᶜ
    E E′ F : Effs
```

## Ground types

```
data Ground : Type → Set where
  $_
    :  (ι : Base)
       ------------
    →  Ground ($ ι)

  ★⇒★
    :  --------------
       Ground (★ ⇒ ⟨ ¿ ⟩ ★)
```

Extract type from evidence that it is ground
```
ground : ∀ {G} → (g : Ground G) → Type
ground {G = G} g  =  G
```

Evidence for a ground type is unique.
```
uniqueG : ∀ {G} → (g : Ground G) → (h : Ground G) → g ≡ h
uniqueG ($ ι) ($ .ι) = refl
uniqueG ★⇒★   ★⇒★    = refl
```

Star is not ground
```
G≢★ : ∀ {G} → (g : Ground G) → G ≢ ★
G≢★ () refl
```

Decision procedure for whether a type is ground.
```
Ground? : ∀(A : Type) → Dec (Ground A)
Ground? ★                                 =  no λ ()
Ground? ($ ι)                             =  yes ($ ι)
Ground? (A ⇒ B) with A ≡? ★   | B ≡ᶜ? ⟨ ¿ ⟩ ★
...                | yes refl | yes refl  =  yes ★⇒★
...                | no  A≢★  | _         =  no  λ{★⇒★ → A≢★ refl}
...                | _        | no  B≢★   =  no  λ{★⇒★ → B≢★ refl}
```

## Precision

```
infix 4 _≤_ _≤ᵉ_ _≤ᶜ_
infixl 5 _⇑_

data _≤ᵉ_ : (_ _ : Effs) → Set where
  id : E ≤ᵉ E
  ¡≤¿ : ∀ {E} → ¡ E ≤ᵉ ¿

record _≤ᶜ_ (_ _ : Typeᶜ) : Set

data _≤_ : Type → Type → Set where

  id : ∀ {A}
      -----
    → A ≤ A

  _⇑_ : ∀ {A G}
    → A ≤ G
    → Ground G
      -----
    → A ≤ ★

  _⇒_ : ∀ {A B A′ B′}
    → A ≤ A′
    → B ≤ᶜ B′
      ---------------
    → A ⇒ B ≤ A′ ⇒ B′

record _≤ᶜ_ P Q where
  inductive
  constructor ⟨_⟩_
  field
    effects : Typeᶜ.effects P ≤ᵉ Typeᶜ.effects Q
    returns : Typeᶜ.returns P ≤  Typeᶜ.returns Q
```

Domain and codomain of function precision.

```
dom : ∀ {A B A′ B′} → A ⇒ B ≤ A′ ⇒ B′ → A ≤ A′
dom id       =  id
dom (p ⇒ q)  =  p

cod : ∀ {A B A′ B′} → A ⇒ B ≤ A′ ⇒ B′ → B ≤ᶜ B′
cod id       =  ⟨ id ⟩ id
cod (p ⇒ q)  =  q
```

The use of these two functions is reminiscent of some gradually-typed
source languages, where one defines

    dom ★        =  ★
    dom (A ⇒ B)  =  A

    cod ★        =  ★
    cod (A ⇒ B)  =  B

and has a typing rules resembling

    Γ ⊢ L : A
    Γ ⊢ M : dom A
    ------------------
    Γ ⊢ L · M : cod A

Our dom and cod will play a similar role when we define the
precedence rules for abstraction and application.

Lemma. Every ground type is more precise than ★.
```
G≤★ : ∀ {G} → Ground G → G ≤ ★
G≤★ ($ ι)  =  id ⇑ $ ι
G≤★ ★⇒★    =  (id ⇒ ⟨ id ⟩ id) ⇑ ★⇒★
```

Lemma. ★ is not more precise than any ground type.
```
¬★≤G : ∀ {G} → Ground G → ¬ (★ ≤ G)
¬★≤G ($ ι) ()
¬★≤G ★⇒★   ()
```

Lemma. ★ is least precise.
```
★≤ : ∀ {A} → ★ ≤ A → A ≡ ★
★≤ {★} p  =  refl
★≤ {$ ι} ()
★≤ {A ⇒ B} ()
```

```
E≤¿ : ∀ {E} → E ≤ᵉ ¿
E≤¿ {¿} = id
E≤¿ {¡ E} = ¡≤¿
```

Lemma. Every type is more precise that ★. (Not true in general.)
```
A≤★ : ∀ {A} → A ≤ ★
A≤★ {★}      =  id
A≤★ {$ ι}    =  id ⇑ $ ι
A≤★ {A ⇒ B}  =  (A≤★ ⇒ ⟨ E≤¿ ⟩ A≤★) ⇑ ★⇒★
```

Lemma. Every type is either ★ or more precise than a ground type. (Not true in general.)
```
★⊎G : ∀ A → (A ≡ ★) ⊎ ∃[ G ](Ground G × A ≤ G)
★⊎G ★        =  inj₁ refl
★⊎G ($ ι)    =  inj₂ ($ ι , $ ι , id)
★⊎G (A ⇒ B)  =  inj₂ (★ ⇒ ⟨ ¿ ⟩ ★ , ★⇒★ , A≤★ ⇒ ⟨ E≤¿ ⟩ A≤★)
```

Lemma. If a type is more precise than a ground type, it is not ★.
```
≢★ : ∀ {A G} → Ground G → A ≤ G → A ≢ ★
≢★ g A≤G A≡★ rewrite A≡★ = ¬★≤G g A≤G
```

Lemma. ≤ is transitive
```
_⨟ᵉ_ : ∀ {A B C} → A ≤ᵉ B → B ≤ᵉ C → A ≤ᵉ C
d ⨟ᵉ id = d
id ⨟ᵉ ¡≤¿ = ¡≤¿

_⨟ᶜ_ : ∀ {A B C} → A ≤ᶜ B → B ≤ᶜ C → A ≤ᶜ C
_⨟_ : ∀ {A B C} → A ≤ B → B ≤ C → A ≤ C
p ⨟ id                     =  p
p ⨟ (q ⇑ g)                =  (p ⨟ q) ⇑ g
_⨟_ {A = _ ⇒ _} p (q ⇒ r)  =  (dom p ⨟ q) ⇒ (cod p ⨟ᶜ r)

(⟨ d ⟩ p) ⨟ᶜ (⟨ e ⟩ q) = ⟨ d ⨟ᵉ e ⟩ (p ⨟ q)
```

Lemmas. Left and right identity.
```
left-idᵉ : ∀ {A B} → (p : A ≤ᵉ B) → id ⨟ᵉ p ≡ p
left-idᵉ id = refl
left-idᵉ ¡≤¿ = refl

left-idᶜ : ∀ {A B} → (p : A ≤ᶜ B) → (⟨ id ⟩ id) ⨟ᶜ p ≡ p

left-id : ∀ {A B} → (p : A ≤ B) → id ⨟ p ≡ p
left-id id                                     =  refl
left-id (p ⇑ g) rewrite left-id p              =  refl
left-id (p ⇒ q) rewrite left-id p | left-idᶜ q =  refl

left-idᶜ (⟨ d ⟩ p) rewrite left-idᵉ d | left-id p = refl
```

```
right-id : ∀ {A B} → (p : A ≤ B) → p ⨟ id {B} ≡ p
right-id p  =  refl
```

Lemma. Associativity.
```
assocᵉ : ∀ {A B C D} (p : A ≤ᵉ B) (q : B ≤ᵉ C) (r : C ≤ᵉ D)
  → (p ⨟ᵉ q) ⨟ᵉ r ≡ p ⨟ᵉ (q ⨟ᵉ r)
assocᵉ p q id = refl
assocᵉ id id ¡≤¿ = refl

assocᶜ : ∀ {A B C D} (p : A ≤ᶜ B) (q : B ≤ᶜ C) (r : C ≤ᶜ D)
  → (p ⨟ᶜ q) ⨟ᶜ r ≡ p ⨟ᶜ (q ⨟ᶜ r)

assoc : ∀ {A B C D} (p : A ≤ B) (q : B ≤ C) (r : C ≤ D)
  → (p ⨟ q) ⨟ r ≡ p ⨟ (q ⨟ r)
assoc p q id                                     = refl
assoc p id r rewrite left-id r                   = refl
assoc id q r rewrite left-id q | left-id (q ⨟ r) = refl
assoc p q (r ⇑ g) rewrite assoc p q r            = refl
assoc (p ⇒ p′) (q ⇒ q′) (r ⇒ r′) rewrite assoc p q r | assocᶜ p′ q′ r′   =  refl

assocᶜ (⟨ d ⟩ p) (⟨ e ⟩ q) (⟨ f ⟩ r)
  rewrite assocᵉ d e f | assoc p q r = refl
```

## Lemma. dom and cod are functors

```
dom-⨟ : ∀ {A B A′ B′ A″ B″} (p : A ⇒ B ≤ A′ ⇒ B′) (q : A′ ⇒ B′ ≤  A″ ⇒ B″)
    → dom p ⨟ dom q ≡ dom (p ⨟ q)
dom-⨟ id id = refl
dom-⨟ id (_ ⇒ _) = refl
dom-⨟ (_ ⇒ _) id = refl
dom-⨟ (_ ⇒ _) (_ ⇒ _) = refl

cod-⨟ : ∀ {A B A′ B′ A″ B″} (p : A ⇒ B ≤ A′ ⇒ B′) (q : A′ ⇒ B′ ≤  A″ ⇒ B″)
    → cod p ⨟ᶜ cod q ≡ cod (p ⨟ q)
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

Decision procedure for precision.
```
infix 4 _≤?_ _≤ᵉ?_ _≤ᶜ?_

_≤ᵉ?_ : Decidable _≤ᵉ_
_ ≤ᵉ? ¿ = yes E≤¿
¡ E ≤ᵉ? ¡ F with E ≟ F
... | yes refl = yes id
... | no ¬≡ = no λ{ id → ¬≡ refl }
¿ ≤ᵉ? ¡ _ = no λ()

_≤ᶜ?_ : Decidable _≤ᶜ_

_≤?_ : (A : Type) → (B : Type) → Dec (A ≤ B)
★ ≤? ★                                           =  yes id
★ ≤? ($ ι)                                       =  no (λ ())
★ ≤? (A ⇒ B)                                     =  no (λ ())
($ ι) ≤? ★                                       =  yes (id ⇑ $ ι)
($ ι) ≤? ($ ι′)       with ι ≡$? ι′
...                     | yes refl               =  yes id
...                     | no  ι≢ι′               =  no  λ{id → ι≢ι′ refl}
($ ι) ≤? (A ⇒ B)                                 =  no (λ ())
(A ⇒ B) ≤? ★         with A ≤? ★ ×-dec B ≤ᶜ? (⟨ ¿ ⟩ ★)
...                     | yes (A≤★ , B≤★) = yes ((A≤★ ⇒ B≤★) ⇑ ★⇒★)
...                     | no  ¬≤          = no  λ{((A≤★ ⇒ B≤★) ⇑ ★⇒★) → ¬≤ (A≤★ , B≤★);
                                                  (id ⇑ ★⇒★)          → ¬≤ (id , ⟨ id ⟩ id)}
(A ⇒ B) ≤? ($ ι)                                 =  no  (λ ())
(A ⇒ B) ≤? (A′ ⇒ B′) with A ≤? A′ ×-dec B ≤ᶜ? B′
...                     | yes (A≤A′ , B≤B′) = yes (A≤A′ ⇒ B≤B′)
...                     | no  ¬≤ =  no  λ{(A≤A′ ⇒ B≤B′) → ¬≤ (A≤A′ , B≤B′);
                                          id            → ¬≤ (id , ⟨ id ⟩ id)}

⟨ E ⟩ A ≤ᶜ? ⟨ F ⟩ B with E ≤ᵉ? F ×-dec A ≤? B
... | yes (E≤ , A≤) = yes (⟨ E≤ ⟩ A≤)
... | no ¬≤ = no λ{ (⟨ E≤ ⟩ A≤) → ¬≤ (E≤ , A≤) }
```

```
_∈¿?_ : Decidable _∈¿_
e ∈¿? ¿ = yes ¿
e ∈¿? (¡ E) with e ∈? E
... | yes e∈E = yes (¡ e∈E)
... | no ¬e∈E = no λ{ (¡ e∈E) → ¬e∈E e∈E }
```

```
∈-≤ : ∀ {e} → E ≤ᵉ F → e ∈¿ E → e ∈¿ F
∈-≤ id e∈E = e∈E
∈-≤ ¡≤¿ _ = ¿
```
