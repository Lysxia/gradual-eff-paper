Simple Blame Calculus with proof relevant casts.
Uses polarity to unify upcasts and downcasts.
Uses nested evaluation contexts.

Siek, Thiemann, and Wadler

```
module Core where

open import Utils
open import Type

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List.Base using (List; [])
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Binary.PropositionalEquality
     using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app; subst; inspect)
     renaming ([_] to [[_]])
open import Relation.Binary using (Decidable)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Product using (_×-dec_)
```

* Contexts and Variables

```
infixl 6 _▷_

data Context : Set where
  ∅   : Context
  _▷_ : Context → Type → Context

infix  4 _∋_
infix  9 S_

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ----------
    → Γ ▷ A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ ▷ B ∋ A
```

```
private
  variable
    A A′ B G : Type
    P P′ Q Q′ : Typeᶜ
    E E′ F : Effs
    Γ : Context
```

## Casts

```
infix  6 _=>_ _=>ᵉᵛ_ _=>ᵉ_
infix  6 _==>_
infix  4 +_
infix  4 -_
```


Cast
```
data _=>_ (A B : Type) : Set where

  +_ : A ≤ B
      ------
     → A => B

  -_ : B ≤ A
      ------
     → A => B

data _=>ᵉ_ (E F : Effs) : Set where

  +_ : E ≤ᵉ F
       -------
     → E =>ᵉ F

  -_ : F ≤ᵉ E
       -------
     → E =>ᵉ F

-- This is a trick to decompose the parameters
-- in the definition of a record.
module _ (P Q : Typeᶜ) (let ⟨ E ⟩ A = P ; ⟨ F ⟩ B = Q) where
  infix 6 _=>ᶜ_
  record _=>ᶜ_ : Set where
    constructor ⟨_⟩_
    field
      effects : E =>ᵉ F
      returns : A => B

-- The two types of casts are kept separate
-- because they have different roles in the operational semantics.
-- This avoid quantifying on extra variables for the casts that are irrelevant
-- to a given reduction rule.

data _=>ᵉᵛ_ : (_ _ : Typeᶜ) → Set where
  ⟨_⟩- : E =>ᵉ F → ⟨ E ⟩ A =>ᵉᵛ ⟨ F ⟩ A
  ⟨-⟩_ : A =>  B → ⟨ E ⟩ A =>ᵉᵛ ⟨ E ⟩ B
```

Decomposing a cast
```
data _==>_ : Type → Type → Set where

  id : ∀ {A}
      -------
    → A ==> A

  _⇒_ : ∀ {A A′ B B′}
    → A′ => A
    → B =>ᶜ B′
      -----------------
    → A ⇒ B ==> A′ ⇒ B′

  other : ∀ {A B}
      -------
    → A ==> B

+ᶜ_ : P ≤ᶜ Q → P =>ᶜ Q
+ᶜ (⟨ E≤ ⟩ p) = ⟨ + E≤ ⟩ (+ p)

-ᶜ_ : Q ≤ᶜ P → P =>ᶜ Q
-ᶜ (⟨ E≤ ⟩ p) = ⟨ - E≤ ⟩ (- p)

split : ∀ {A B} → A => B → A ==> B
split (+ id)     =  id
split (- id)     =  id
split (+ s ⇒ t)  =  (- s) ⇒ (+ᶜ t)
split (- s ⇒ t)  =  (+ s) ⇒ (-ᶜ t)
split (+ p ⇑ g)  =  other
split (- p ⇑ g)  =  other
```

## Terms

```
infix  4 _⊢_
infix  4 _⊢_➡_
infixl 5 _＠_
infixl 5 _＠⟨⟩_
infixl 5 _＠⟨_⟩
infix  6 _·_
infix  6 _⦅_⦆_
infix  8 `_

record _⊢_➡_ (Γ : Context) (P Q : Typeᶜ) : Set

data _⊢_ : Context → Typeᶜ → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ ⟨ E ⟩ A

  ƛ_ :  ∀ {Γ E F B A}
    → Γ ▷ A ⊢ ⟨ F ⟩ B
      ---------
    → Γ ⊢ ⟨ E ⟩ (A ⇒ ⟨ F ⟩ B)

  _·_ : ∀ {Γ E A B}
    → Γ ⊢ ⟨ E ⟩ (A ⇒ ⟨ E ⟩ B)
    → Γ ⊢ ⟨ E ⟩ A
      ---------
    → Γ ⊢ ⟨ E ⟩ B

  $_ : ∀ {ι}
    → rep ι
      -------
    → Γ ⊢ ⟨ E ⟩ ($ ι)

  _⦅_⦆_ : ∀ {Γ E ι ι′ ι″}
    → Γ ⊢ ⟨ E ⟩ ($ ι)
    → (rep ι → rep ι′ → rep ι″)
    → Γ ⊢ ⟨ E ⟩ ($ ι′)
      ----------------------
    → Γ ⊢ ⟨ E ⟩ ($ ι″)

  _⇑_ : ∀ {Γ G E}
    → Γ ⊢ ⟨ E ⟩ G
    → Ground G
      -----
    → Γ ⊢ ⟨ E ⟩ ★

  blame : ∀ {Γ A}
      -----
    → Γ ⊢ A

  -- Fording (response e ≡ A) helps pattern matching.
  perform- : ∀ {e}
    → e ∈¿ E
    → response e ≡ A
    → Γ ⊢ ⟨ E ⟩ request e
      --------------------
    → Γ ⊢ ⟨ E ⟩ A

  handle :
      Γ ⊢ P ➡ Q
    → Γ ⊢ P
      ---------
    → Γ ⊢ Q

  _＠⟨⟩_ : ∀ {Γ P Q}
    → Γ ⊢ P
    → P =>ᵉᵛ Q
      ------
    → Γ ⊢ Q

On-Perform : Context → Typeᶜ → List 𝔼 → Set
On-Perform Γ Q Hooks = All (λ e → Γ ▷ request e ▷ (response e ⇒ Q) ⊢ Q) Hooks

record _⊢_➡_ Γ P Q where
  inductive
  open Typeᶜ
  field
    Hooks : List 𝔼
    Hooks-handled : P .effects ≡ (Hooks ++¿ Q .effects)
    on-return : Γ ▷ P .returns ⊢ Q
    on-perform : On-Perform Γ Q Hooks

open _⊢_➡_ public
```

```
pattern perform e∈E M = perform- e∈E refl M
pattern _＠_ M ±p = M ＠⟨⟩ ⟨-⟩ ±p
pattern _＠⟨_⟩ M ±p = M ＠⟨⟩ ⟨ ±p ⟩-
```

## Renaming maps, substitution maps, term maps

```
infix 4 _→ᴿ_ _→ˢ_ _→ᵀ_ _→ʰ_

_→ᴿ_ : Context → Context → Set
Γ →ᴿ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

_→ˢ_ : Context → Context → Set
Γ →ˢ Δ = ∀ {E A} → Γ ∋ A → Δ ⊢ ⟨ E ⟩ A

_→ᵀ_ : Context → Context → Set
Γ →ᵀ Δ = ∀ {A} → Γ ⊢ A → Δ ⊢ A

_→ʰ_ : Context → Context → Set
Γ →ʰ Δ = ∀ {P Q} → Γ ⊢ P ➡ Q → Δ ⊢ P ➡ Q
```


## Renaming

Extension of renaming maps
```
ren▷ : ∀ {Γ Δ A}
  → (Γ →ᴿ Δ)
    ----------------------------
  → ((Γ ▷ A) →ᴿ (Δ ▷ A))
ren▷ ρ Z      =  Z
ren▷ ρ (S x)  =  S (ρ x)

ren : ∀ {Γ Δ}
  → (Γ →ᴿ Δ)
    --------
  → (Γ →ᵀ Δ)

ren-on-perform : ∀ {Γ Δ} → (Γ →ᴿ Δ) → ∀ {Q Hooks} → On-Perform Γ Q Hooks → On-Perform Δ Q Hooks
ren-on-perform ρ [] = []
ren-on-perform ρ (M ∷ Ms) = ren (ren▷ (ren▷ ρ)) M ∷ ren-on-perform ρ Ms

renʰ : ∀ {Γ Δ} → (Γ →ᴿ Δ) → (Γ →ʰ Δ)
renʰ ρ H = record
  { Hooks = Hooks H
  ; Hooks-handled = Hooks-handled H
  ; on-return = ren (ren▷ ρ) (on-return H)
  ; on-perform = ren-on-perform ρ (on-perform H) }

ren ρ (` x)          = ` (ρ x)
ren ρ (ƛ N)          =  ƛ (ren (ren▷ ρ) N)
ren ρ (L · M)        =  (ren ρ L) · (ren ρ M)
ren ρ ($ k)          =  $ k
ren ρ (L ⦅ _⊕_ ⦆ M)  =  (ren ρ L) ⦅ _⊕_ ⦆ (ren ρ M)
ren ρ (M ⇑ g)        =  (ren ρ M) ⇑ g
ren ρ (M ＠⟨⟩ ±p )     =  (ren ρ M) ＠⟨⟩ ±p
ren ρ blame          =  blame
ren ρ (perform- e∈E eq M)  = perform- e∈E eq (ren ρ M)
ren ρ (handle H M)   = handle (renʰ ρ H) (ren ρ M)

lift : ∀ {Γ : Context} {A : Type} → Γ →ᵀ (Γ ▷ A)
lift = ren S_
```

## Substitution

```
sub▷ : ∀ {Γ Δ A}
  → (Γ →ˢ Δ)
    --------------------------
  → ((Γ ▷ A) →ˢ (Δ ▷ A))
sub▷ σ Z      =  ` Z
sub▷ σ (S x)  =  lift (σ x)

sub : ∀ {Γ Δ : Context}
  → (Γ →ˢ Δ)
    --------
  → (Γ →ᵀ Δ)

sub-on-perform : ∀ {Γ Δ} → (Γ →ˢ Δ) → ∀ {Q Hooks} → On-Perform Γ Q Hooks → On-Perform Δ Q Hooks
sub-on-perform σ [] = []
sub-on-perform σ (M ∷ Ms) = sub (sub▷ (sub▷ σ)) M ∷ sub-on-perform σ Ms

subʰ : ∀ {Γ Δ} → (Γ →ˢ Δ) → (Γ →ʰ Δ)
subʰ σ H = record
  { Hooks = Hooks H
  ; Hooks-handled = Hooks-handled H
  ; on-return = sub (sub▷ σ) (on-return H)
  ; on-perform = sub-on-perform σ (on-perform H) }

sub σ (` x)          =  σ x
sub σ (ƛ  N)         =  ƛ (sub (sub▷ σ) N)
sub σ (L · M)        =  (sub σ L) · (sub σ M)
sub σ ($ k)          =  $ k
sub σ (L ⦅ _⊕_ ⦆ M)  =  (sub σ L) ⦅ _⊕_ ⦆ (sub σ M)
sub σ (M ⇑ g)        =  (sub σ M) ⇑ g
sub σ (M ＠⟨⟩ ±p)     =  (sub σ M) ＠⟨⟩ ±p
sub σ blame          =  blame
sub σ (perform- e∈E eq M) = perform- e∈E eq (sub σ M)
sub ρ (handle H M)   = handle (subʰ ρ H) (sub ρ M)
```

Special case of substitution, used in beta rule
```
σ₀ : ∀ {Γ A} → (M : ∀ {E} → Γ ⊢ ⟨ E ⟩ A) → (Γ ▷ A) →ˢ Γ
σ₀ M Z      =  M
σ₀ M (S x)  =  ` x

_[_] : Γ ▷ A ⊢ P
     → (∀ {E} → Γ ⊢ ⟨ E ⟩ A)
       ---------
     → Γ ⊢ P
_[_] {Γ} {A} N M =  sub {Γ ▷ A} {Γ} (σ₀ M) N
```

## Composition and identity

Rename composed with rename

```
ren∘ren▷ : ∀ {Γ Γ′ Γ″} {ρ : Γ →ᴿ Γ′} {ρ′ : Γ′ →ᴿ Γ″} {ρ″ : Γ →ᴿ Γ″}
  → (∀ {A} (x : Γ ∋ A) → ρ′ (ρ x) ≡ ρ″ x)
    --------------------------------------------------------------
  → (∀ {B A} (x : Γ ▷ B ∋ A) → ren▷ ρ′ (ren▷ ρ x) ≡ ren▷ ρ″ x)
ren∘ren▷ ρ∘ Z      =  refl
ren∘ren▷ ρ∘ (S x)  =  cong S_ (ρ∘ x)

ren∘ren : ∀ {Γ Γ′ Γ″} {ρ : Γ →ᴿ Γ′} {ρ′ : Γ′ →ᴿ Γ″} {ρ″ : Γ →ᴿ Γ″}
  → (∀ {A} (x : Γ ∋ A) → ρ′ (ρ x) ≡ ρ″ x)
    -------------------------------------------------
  → (∀ {A} (M : Γ ⊢ A) → ren ρ′ (ren ρ M) ≡ ren ρ″ M)

ren∘ren-on-perform :  ∀ {Γ Γ′ Γ″} {ρ : Γ →ᴿ Γ′} {ρ′ : Γ′ →ᴿ Γ″} {ρ″ : Γ →ᴿ Γ″}
  → (∀ {A} (x : Γ ∋ A) → ρ′ (ρ x) ≡ ρ″ x)
    -------------------------------------------------
  → (∀ {Hooks Q} (H : On-Perform Γ Q Hooks) → ren-on-perform ρ′ (ren-on-perform ρ H) ≡ ren-on-perform ρ″ H)
ren∘ren-on-perform ρ≡ [] = refl
ren∘ren-on-perform ρ≡ (M ∷ Ms) = cong₂ _∷_ (ren∘ren (ren∘ren▷ (ren∘ren▷ ρ≡)) M) (ren∘ren-on-perform ρ≡ Ms)

ren∘renʰ :  ∀ {Γ Γ′ Γ″} {ρ : Γ →ᴿ Γ′} {ρ′ : Γ′ →ᴿ Γ″} {ρ″ : Γ →ᴿ Γ″}
  → (∀ {A} (x : Γ ∋ A) → ρ′ (ρ x) ≡ ρ″ x)
    -------------------------------------------------
  → (∀ {P Q} (H : Γ ⊢ P ➡ Q) → renʰ ρ′ (renʰ ρ H) ≡ renʰ ρ″ H)
ren∘renʰ ρ≡ H = cong₂
  (λ M Ns → record { on-return = M ; on-perform = Ns })
  (ren∘ren (ren∘ren▷ ρ≡) (on-return H)) (ren∘ren-on-perform ρ≡ (on-perform H))

ren∘ren ρ≡ (` x)          =  cong `_ (ρ≡ x)
ren∘ren ρ≡ (ƛ N)          =  cong ƛ_ (ren∘ren (ren∘ren▷ ρ≡) N)
ren∘ren ρ≡ (L · M)        =  cong₂ _·_ (ren∘ren ρ≡ L) (ren∘ren ρ≡ M)
ren∘ren ρ≡ ($ k)          =  refl
ren∘ren ρ≡ (L ⦅ _⊕_ ⦆ M)  =  cong₂ _⦅ _⊕_ ⦆_ (ren∘ren ρ≡ L) (ren∘ren ρ≡ M)
ren∘ren ρ≡ (M ⇑ g)        =  cong (_⇑ g) (ren∘ren ρ≡ M)
ren∘ren ρ≡ (M ＠⟨⟩ ±p )     =  cong (_＠⟨⟩ ±p) (ren∘ren ρ≡ M)
ren∘ren ρ≡ blame          =  refl
ren∘ren ρ≡ (perform- e∈E eq M) = cong (perform- e∈E eq) (ren∘ren ρ≡ M)
ren∘ren {ρ = ρ} {ρ′ = ρ′} ρ≡ (handle H M) = cong₂ handle (ren∘renʰ {ρ = ρ} {ρ′ = ρ′} ρ≡ H) (ren∘ren ρ≡ M)

lift∘ren : ∀ {Γ Δ A B} (ρ : Γ →ᴿ Δ) (M : Γ ⊢ B)
  → lift {A = A} (ren ρ M) ≡ ren (ren▷ ρ) (lift {A = A} M)
lift∘ren {Γ} ρ M  =  trans (ren∘ren ρ≡₁ M) (sym (ren∘ren ρ≡₂ M))
  where
  ρ≡₁ : ∀ {A} (x : Γ ∋ A) → S (ρ x) ≡ S (ρ x)
  ρ≡₁ x = refl
  ρ≡₂ : ∀ {A} (x : Γ ∋ A) → ren▷ ρ (S x) ≡ S (ρ x)
  ρ≡₂ Z     = refl
  ρ≡₂ (S x) = refl

sub∘ren▷ : ∀ {Γ Γ′ Γ″} {ρ : Γ →ᴿ Γ′} {σ′ : Γ′ →ˢ Γ″} {σ″ : Γ →ˢ Γ″}
  → (∀ {E A} (x : Γ ∋ A) → σ′ {E} (ρ x) ≡ σ″ x)
    ----------------------------------------------------------
  → (∀ {E B A} (x : Γ ▷ B ∋ A) → sub▷ σ′ {E} (ren▷ ρ x) ≡ sub▷ σ″ x)
sub∘ren▷ σ≡ Z      =  refl
sub∘ren▷ σ≡ (S x)  =  cong (ren S_) (σ≡ x)

sub∘ren : ∀ {Γ Γ′ Γ″} {ρ : Γ →ᴿ Γ′} {σ′ : Γ′ →ˢ Γ″} {σ″ : Γ →ˢ Γ″}
  → (∀ {E A} (x : Γ ∋ A) → σ′ {E} (ρ x) ≡ σ″ x)
    ----------------------------------------------------------
  → (∀ {A} (M : Γ ⊢ A) → sub σ′ (ren ρ M) ≡ sub σ″ M)

sub∘ren-on-perform :  ∀ {Γ Γ′ Γ″} {ρ : Γ →ᴿ Γ′} {σ′ : Γ′ →ˢ Γ″} {σ″ : Γ →ˢ Γ″}
  → (∀ {E A} (x : Γ ∋ A) → σ′ {E} (ρ x) ≡ σ″ x)
    -------------------------------------------------
  → (∀ {Hooks Q} (H : On-Perform Γ Q Hooks) → sub-on-perform σ′ (ren-on-perform ρ H) ≡ sub-on-perform σ″ H)
sub∘ren-on-perform ρ≡ [] = refl
sub∘ren-on-perform ρ≡ (M ∷ Ms) = cong₂ _∷_ (sub∘ren (sub∘ren▷ (sub∘ren▷ ρ≡)) M) (sub∘ren-on-perform ρ≡ Ms)

sub∘renʰ :  ∀ {Γ Γ′ Γ″} {ρ : Γ →ᴿ Γ′} {σ′ : Γ′ →ˢ Γ″} {σ″ : Γ →ˢ Γ″}
  → (∀ {E A} (x : Γ ∋ A) → σ′ {E} (ρ x) ≡ σ″ x)
    -------------------------------------------------
  → (∀ {P Q} (H : Γ ⊢ P ➡ Q) → subʰ σ′ (renʰ ρ H) ≡ subʰ σ″ H)
sub∘renʰ ρ≡ H = cong₂
  (λ M Ns → record { on-return = M ; on-perform = Ns })
  (sub∘ren (sub∘ren▷ ρ≡) (on-return H))
  (sub∘ren-on-perform ρ≡ (on-perform H))

sub∘ren σ≡ (` x)          =  σ≡ x
sub∘ren σ≡ (ƛ N)          =  cong ƛ_ (sub∘ren (sub∘ren▷ σ≡) N)
sub∘ren σ≡ (L · M)        =  cong₂ _·_ (sub∘ren σ≡ L) (sub∘ren σ≡ M)
sub∘ren σ≡ ($ k)          =  refl
sub∘ren σ≡ (L ⦅ _⊕_ ⦆ M)  =  cong₂ _⦅ _⊕_ ⦆_ (sub∘ren σ≡ L) (sub∘ren σ≡ M)
sub∘ren σ≡ (M ⇑ g)        =  cong (_⇑ g) (sub∘ren σ≡ M)
sub∘ren σ≡ (M ＠⟨⟩ ±p)     =  cong (_＠⟨⟩ ±p) (sub∘ren σ≡ M)
sub∘ren σ≡ blame          =  refl
sub∘ren ρ≡ (perform- e∈E eq M) = cong (perform- e∈E eq) (sub∘ren ρ≡ M)
sub∘ren {ρ = ρ} {σ′ = σ′} ρ≡ (handle H M)   = cong₂ handle (sub∘renʰ {ρ = ρ} {σ′ = σ′} ρ≡ H) (sub∘ren ρ≡ M)

ren∘sub▷ : ∀ {Γ Γ′ Γ″} {σ : Γ →ˢ Γ′} {ρ′ : Γ′ →ᴿ Γ″} {σ″ : Γ →ˢ Γ″}
  → (∀ {E A} (x : Γ ∋ A) → ren ρ′ (σ {E} x) ≡ σ″ x)
    -------------------------------------------------------------------
  → (∀ {E B A} (x : Γ ▷ B ∋ A) → ren (ren▷ ρ′) (sub▷ σ {E} x) ≡ sub▷ σ″ x)
ren∘sub▷ σ≡ Z      =  refl
ren∘sub▷ {Γ′ = Γ′} {σ = σ} {ρ′ = ρ′} σ≡ {B = B} (S x)  =
    trans (trans (ren∘ren ρ∘₁ (σ x)) (sym (ren∘ren ρ∘₂ (σ x)))) (cong (ren S_) (σ≡ x))
  where
  ρ∘₁ : ∀ {A} (x : Γ′ ∋ A) → ren▷ {A = B} ρ′ (S_ x) ≡ S (ρ′ x)
  ρ∘₁ x = refl

  ρ∘₂ : ∀ {A} (x : Γ′ ∋ A) → S_ {B = B} (ρ′ x) ≡ S (ρ′ x)
  ρ∘₂ x = refl

ren∘sub : ∀ {Γ Γ′ Γ″} {σ : Γ →ˢ Γ′} {ρ′ : Γ′ →ᴿ Γ″} {σ″ : Γ →ˢ Γ″}
  → (∀ {E A} (x : Γ ∋ A) → ren ρ′ (σ {E} x) ≡ σ″ x)
    --------------------------------------------------------
  → (∀ {A} (M : Γ ⊢ A) → ren ρ′ (sub σ M) ≡ sub σ″ M)

ren∘sub-on-perform :  ∀ {Γ Γ′ Γ″} {ρ : Γ →ˢ Γ′} {ρ′ : Γ′ →ᴿ Γ″} {ρ″ : Γ →ˢ Γ″}
  → (∀ {E A} (x : Γ ∋ A) → ren ρ′ (ρ {E} x) ≡ ρ″ x)
    -------------------------------------------------
  → (∀ {Hooks Q} (H : On-Perform Γ Q Hooks) → ren-on-perform ρ′ (sub-on-perform ρ H) ≡ sub-on-perform ρ″ H)
ren∘sub-on-perform ρ≡ [] = refl
ren∘sub-on-perform ρ≡ (M ∷ Ms) = cong₂ _∷_ (ren∘sub (ren∘sub▷ (ren∘sub▷ ρ≡)) M) (ren∘sub-on-perform ρ≡ Ms)

ren∘subʰ :  ∀ {Γ Γ′ Γ″} {σ : Γ →ˢ Γ′} {ρ′ : Γ′ →ᴿ Γ″} {σ″ : Γ →ˢ Γ″}
  → (∀ {E A} (x : Γ ∋ A) → ren ρ′ (σ {E} x) ≡ σ″ x)
    -------------------------------------------------
  → (∀ {P Q} (H : Γ ⊢ P ➡ Q) → renʰ ρ′ (subʰ σ H) ≡ subʰ σ″ H)
ren∘subʰ ρ≡ H = cong₂
  (λ M Ns → record { on-return = M ; on-perform = Ns })
  (ren∘sub (ren∘sub▷ ρ≡) (on-return H))
  (ren∘sub-on-perform ρ≡ (on-perform H))

ren∘sub σ≡ (` x)          =  σ≡ x
ren∘sub σ≡ (ƛ N)          =  cong ƛ_ (ren∘sub (ren∘sub▷ σ≡) N)
ren∘sub σ≡ (L · M)        =  cong₂ _·_ (ren∘sub σ≡ L) (ren∘sub σ≡ M)
ren∘sub σ≡ ($ k)          =  refl
ren∘sub σ≡ (L ⦅ _⊕_ ⦆ M)  =  cong₂ _⦅ _⊕_ ⦆_ (ren∘sub σ≡ L) (ren∘sub σ≡ M)
ren∘sub σ≡ (M ⇑ g)        =  cong (_⇑ g) (ren∘sub σ≡ M)
ren∘sub σ≡ (M ＠⟨⟩ ±p)     =  cong (_＠⟨⟩ ±p) (ren∘sub σ≡ M)
ren∘sub σ≡ blame          =  refl
ren∘sub ρ≡ (perform- e∈E eq M) = cong (perform- e∈E eq) (ren∘sub ρ≡ M)
ren∘sub ρ≡ (handle H M)   = cong₂ handle (ren∘subʰ ρ≡ H) (ren∘sub ρ≡ M)

lift∘sub : ∀ {Γ Δ A B} (σ : Γ →ˢ Δ) (M : Γ ⊢ B)
  → lift {A = A} (sub σ M) ≡ sub (sub▷ σ) (lift {A = A} M)
lift∘sub {Γ} σ M  =  trans (ren∘sub σ≡₁ M) (sym (sub∘ren σ≡₂ M))
  where
  σ≡₁ : ∀ {A E} (x : Γ ∋ A) → lift (σ {E} x) ≡ lift (σ x)
  σ≡₁ x = refl
  σ≡₂ : ∀ {A E} (x : Γ ∋ A) → sub▷ σ {E} (S x) ≡ lift (σ x)
  σ≡₂ Z     = refl
  σ≡₂ (S x) = refl
```

## Renaming and substitution by identity is the identity

```
Idᴿ : ∀ {Γ} → (ρ : Γ →ᴿ Γ) → Set
Idᴿ {Γ} ρ  =  ∀ {A} (x : Γ ∋ A) → ρ x ≡ x

Idˢ : ∀ {Γ} → (σ : Γ →ˢ Γ) → Set
Idˢ {Γ} σ  =  ∀ {E A} (x : Γ ∋ A) → σ {E} x ≡ ` x

Idᵀ : ∀ {Γ} → (θ : Γ →ᵀ Γ) → Set
Idᵀ {Γ} θ  =  ∀ {A} (M : Γ ⊢ A) → θ M ≡ M

Idʰ : ∀ {Γ} → (θ : Γ →ʰ Γ) → Set
Idʰ {Γ} θ  =  ∀ {P Q} (H : Γ ⊢ P ➡ Q) → θ H ≡ H

Id-on-perform : ∀ {Γ} → (θ : ∀ {Hooks Q} → On-Perform Γ Q Hooks → On-Perform Γ Q Hooks) → Set
Id-on-perform {Γ} θ  =  ∀ {Hooks Q} (H : On-Perform Γ Q Hooks) → θ H ≡ H

renId▷ : ∀ {Γ} {ρ : Γ →ᴿ Γ}
  → Idᴿ {Γ} ρ
    ----------------------------
  → ∀ {A} → Idᴿ {Γ ▷ A} (ren▷ ρ)
renId▷ ρId Z                    =  refl
renId▷ ρId (S x) rewrite ρId x  =  refl

renId : ∀ {Γ} {ρ : Γ →ᴿ Γ}
  → Idᴿ ρ
    -------------
  → Idᵀ (ren ρ)

renId-on-perform : ∀ {Γ} {ρ : Γ →ᴿ Γ}
  → Idᴿ ρ
    -------------
  → Id-on-perform (ren-on-perform ρ)
renId-on-perform ρId [] = refl
renId-on-perform ρId (M ∷ Ms) = cong₂ _∷_ (renId (renId▷ (renId▷ ρId)) M) (renId-on-perform ρId Ms)

renIdʰ : ∀ {Γ} {ρ : Γ →ᴿ Γ}
  → Idᴿ ρ
    -------------
  → Idʰ (renʰ ρ)
renIdʰ ρId H = cong₂ (λ M Ns → record { on-return = M ; on-perform = Ns }) (renId (renId▷ ρId) (on-return H)) (renId-on-perform ρId (on-perform H))
  where open _⊢_➡_ H

renId ρId (` x) rewrite ρId x                               =  refl
renId ρId (ƛ M) rewrite renId (renId▷ ρId) M                =  refl
renId ρId (L · M) rewrite renId ρId L | renId ρId M         =  refl
renId ρId ($ k)                                             =  refl
renId ρId (L ⦅ _⊕_ ⦆ M) rewrite renId ρId L | renId ρId M   =  refl
renId ρId (M ⇑ g) rewrite renId ρId M                       =  refl
renId ρId (M ＠⟨⟩ ±p) rewrite renId ρId M                   =  refl
renId ρId blame                                             =  refl
renId ρId (perform- e∈E eq M) rewrite renId ρId M           =  refl
renId ρId (handle H M) rewrite renIdʰ ρId H | renId ρId M   = refl

subId▷ : ∀ {Γ} {σ : Γ →ˢ Γ}
  → Idˢ {Γ} σ
    ----------------------------
  → ∀ {A} → Idˢ {Γ ▷ A} (sub▷ σ)
subId▷ σId Z                    =  refl
subId▷ σId {A} {E} (S x) rewrite σId {E} x  =  refl

subId : ∀ {Γ} {σ : Γ →ˢ Γ}
  → Idˢ σ
    -------------
  → Idᵀ (sub σ)

subId-on-perform : ∀ {Γ} {ρ : Γ →ˢ Γ}
  → Idˢ ρ
    -------------
  → Id-on-perform (sub-on-perform ρ)
subId-on-perform ρId [] = refl
subId-on-perform ρId (M ∷ Ms) = cong₂ _∷_ (subId (subId▷ (subId▷ ρId)) M) (subId-on-perform ρId Ms)

subIdʰ : ∀ {Γ} {σ : Γ →ˢ Γ}
  → Idˢ σ
    -------------
  → Idʰ (subʰ σ)
subIdʰ ρId H = cong₂
  (λ M Ns → record { on-return = M ; on-perform = Ns })
  (subId (subId▷ ρId) (on-return H))
  (subId-on-perform ρId (on-perform H))
  where open _⊢_➡_ H

subId σId {⟨ E ⟩ _} (` x) rewrite σId {E} x                 =  refl
subId σId (ƛ M) rewrite subId (subId▷ σId) M                =  refl
subId σId (L · M) rewrite subId σId L | subId σId M         =  refl
subId σId ($ k)                                             =  refl
subId σId (L ⦅ _⊕_ ⦆ M) rewrite subId σId L | subId σId M   =  refl
subId σId (M ⇑ g) rewrite subId σId M                       =  refl
subId σId (M ＠⟨⟩ ±p) rewrite subId σId M                   =  refl
subId σId blame                                             =  refl
subId σId (perform- e∈E eq M) rewrite subId σId M           =  refl
subId ρId (handle H M) rewrite subIdʰ ρId H | subId ρId M   = refl
```

## Values

```
data Value {Γ E} : Γ ⊢ ⟨ E ⟩ A → Set where

  ƛ_ :
      (N : Γ ▷ A ⊢ ⟨ F ⟩ B)
      ---------------
    → Value (ƛ N)

  $_ : ∀{ι}
    → (k : rep ι)
      -------------------
    → Value ($ k)

  _⇑_ : ∀{G}{V : Γ ⊢ ⟨ E ⟩ G}
    → (v : Value V)
    → (g : Ground G)
      ------------------
    → Value (V ⇑ g)
```


Extract term from evidence that it is a value.
```
raw-value : ∀ {Γ P} {V : Γ ⊢ P} → Value V → Γ ⊢ P
raw-value {V = V} _ = V

value : ∀ {Γ A} {V : Γ ⊢ ⟨ E ⟩ A}
  → (v : Value V)
    -------------
  → ∀ {F} → Γ ⊢ ⟨ F ⟩ A
value (ƛ N)  =  ƛ N
value ($ k)  =  $ k
value (V ⇑ g) = value V ⇑ g
```


Renaming preserves values
```
ren-val : ∀ {Γ Δ E A} {V : Γ ⊢ ⟨ E ⟩ A}
  → (ρ : Γ →ᴿ Δ)
  → Value V
    ------------------
  → Value (ren ρ V)
ren-val ρ (ƛ N)    =  ƛ (ren (ren▷ ρ) N)
ren-val ρ ($ k)    =  $ k
ren-val ρ (V ⇑ g)  =  (ren-val ρ V) ⇑ g
```

Substitution preserves values
```
sub-val : ∀ {Γ Δ A} {V : Γ ⊢ ⟨ ε ⟩ A}
  → (σ : Γ →ˢ Δ)
  → Value V
    ------------------
  → Value (sub σ V)
sub-val σ (ƛ N)    =  ƛ (sub (sub▷ σ) N)
sub-val σ ($ k)    =  $ k
sub-val σ (V ⇑ g)  =  (sub-val σ V) ⇑ g
```

## Frames

```
infix  5 [_]⇑_
infix  5 [_]＠⟨⟩_ [_]＠⟨_⟩ [_]＠_
infix  6 [_]·_
infix  6 _·[_]
infix  6 [_]⦅_⦆_
infix  6 _⦅_⦆[_]
infix  7 _⟦_⟧

data Frame (Γ : Context) (C : Typeᶜ) : Typeᶜ → Set where

  □ : Frame Γ C C

  [_]·_ : ∀ {A B}
    → (𝐸 : Frame Γ C (⟨ E ⟩ (A ⇒ ⟨ E ⟩ B)))
    → (M : Γ ⊢ ⟨ E ⟩ A)
      ---------------
    → Frame Γ C (⟨ E ⟩ B)

  _·[_] : ∀ {A B}{V : Γ ⊢ ⟨ E ⟩ (A ⇒ ⟨ E ⟩ B)}
    → (v : Value V)
    → (𝐸 : Frame Γ C (⟨ E ⟩ A))
      ----------------
    → Frame Γ C (⟨ E ⟩ B)

  [_]⦅_⦆_ : ∀ {ι ι′ ι″}
    → (𝐸 : Frame Γ C (⟨ E ⟩ ($ ι)))
    → (_⊕_ : rep ι → rep ι′ → rep ι″)
    → (N : Γ ⊢ ⟨ E ⟩ ($ ι′))
      ------------------
    → Frame Γ C (⟨ E ⟩ ($ ι″))

  _⦅_⦆[_] : ∀ {ι ι′ ι″}{V : Γ ⊢ ⟨ E ⟩ $ ι}
    → (v : Value V)
    → (_⊕_ : rep ι → rep ι′ → rep ι″)
    → (𝐸 : Frame Γ C (⟨ E ⟩ ($ ι′)))
      -------------------
    → Frame Γ C (⟨ E ⟩ ($ ι″))

  [_]⇑_ : ∀ {G}
    → (𝐸 : Frame Γ C (⟨ E ⟩ G))
    → (g : Ground G)
      --------------
    → Frame Γ C (⟨ E ⟩ ★)

  [_]＠⟨⟩_ : ∀ {A B}
    → (𝐸 : Frame Γ C A)
    → (±p : A =>ᵉᵛ B)
      -------------
    → Frame Γ C B

  ″perform_[_]_ : ∀ {e}
    → e ∈¿ E
    → Frame Γ C (⟨ E ⟩ request e)
    → ∀ {A}
    → response e ≡ A
    → Frame Γ C (⟨ E ⟩ A)

  ′handle_[_] :
      Γ ⊢ P ➡ Q
    → Frame Γ C P
      -----------
    → Frame Γ C Q

pattern [_]＠⟨_⟩ 𝐸 ±p = [ 𝐸 ]＠⟨⟩ ⟨ ±p ⟩-
pattern [_]＠_ 𝐸 ±p = [ 𝐸 ]＠⟨⟩ ⟨-⟩ ±p
pattern ′perform_[_] e 𝐸 = ″perform e [ 𝐸 ] refl
```

The plug function inserts an expression into the hole of a frame.
```
_⟦_⟧ : ∀{Γ A B} → Frame Γ A B → Γ ⊢ A → Γ ⊢ B
□ ⟦ M ⟧                 =  M
([ 𝐸 ]· M) ⟦ L ⟧        =  𝐸 ⟦ L ⟧ · M
(v ·[ 𝐸 ]) ⟦ M ⟧        =  raw-value v · 𝐸 ⟦ M ⟧
([ 𝐸 ]⦅ _⊕_ ⦆ N) ⟦ M ⟧  =  𝐸 ⟦ M ⟧ ⦅ _⊕_ ⦆ N
(v ⦅ _⊕_ ⦆[ 𝐸 ]) ⟦ N ⟧  =  raw-value v ⦅ _⊕_ ⦆ 𝐸 ⟦ N ⟧
([ 𝐸 ]⇑ g) ⟦ M ⟧        =  𝐸 ⟦ M ⟧ ⇑ g
([ 𝐸 ]＠⟨⟩ ±p) ⟦ M ⟧    =  (𝐸 ⟦ M ⟧) ＠⟨⟩ ±p
(″perform e∈E [ 𝐸 ] eq) ⟦ M ⟧ = perform- e∈E eq (𝐸 ⟦ M ⟧)
(′handle H [ 𝐸 ]) ⟦ M ⟧ = handle H (𝐸 ⟦ M ⟧)
```

Composition of two frames
```
_∘∘_ : ∀{Γ A B C} → Frame Γ B C → Frame Γ A B → Frame Γ A C
□ ∘∘ 𝐹                 =  𝐹
([ 𝐸 ]· M) ∘∘ 𝐹        =  [ 𝐸 ∘∘ 𝐹 ]· M
(v ·[ 𝐸 ]) ∘∘ 𝐹        =  v ·[ 𝐸 ∘∘ 𝐹 ]
([ 𝐸 ]⦅ _⊕_ ⦆ N) ∘∘ 𝐹  =  [ 𝐸 ∘∘ 𝐹 ]⦅ _⊕_ ⦆ N
(v ⦅ _⊕_ ⦆[ 𝐸 ]) ∘∘ 𝐹  =  v ⦅ _⊕_ ⦆[ 𝐸 ∘∘ 𝐹 ]
([ 𝐸 ]⇑ g) ∘∘ 𝐹        =  [ 𝐸 ∘∘ 𝐹 ]⇑ g
([ 𝐸 ]＠⟨⟩ ±p) ∘∘ 𝐹     =  [ 𝐸 ∘∘ 𝐹 ]＠⟨⟩ ±p
(″perform e∈E [ 𝐸 ] eq) ∘∘ 𝐹 = ″perform e∈E [ 𝐸 ∘∘ 𝐹 ] eq
(′handle H [ 𝐸 ]) ∘∘ 𝐹  =  ′handle H [ 𝐸 ∘∘ 𝐹 ]
```

Composition and plugging
```
∘∘-lemma : ∀ {Γ A B C}
  → (𝐸 : Frame Γ B C)
  → (𝐹 : Frame Γ A B)
  → (M : Γ ⊢ A)
    -----------------------------
  → 𝐸 ⟦ 𝐹 ⟦ M ⟧ ⟧ ≡ (𝐸 ∘∘ 𝐹) ⟦ M ⟧
∘∘-lemma □ 𝐹 M                                         =  refl
∘∘-lemma ([ 𝐸 ]· M₁) 𝐹 M       rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
∘∘-lemma (v ·[ 𝐸 ]) 𝐹 M        rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
∘∘-lemma ([ 𝐸 ]⦅ _⊕_ ⦆ N) 𝐹 M  rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
∘∘-lemma (v ⦅ _⊕_ ⦆[ 𝐸 ]) 𝐹 M  rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
∘∘-lemma ([ 𝐸 ]⇑ g) 𝐹 M        rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
∘∘-lemma ([ 𝐸 ]＠⟨⟩ ±p) 𝐹 M    rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
∘∘-lemma (″perform e∈E [ 𝐸 ] eq) 𝐹 M rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
∘∘-lemma (′handle H [ 𝐸 ]) 𝐹 M rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
```

```
renᶠ : ∀ {Γ Δ} → Γ →ᴿ Δ → Frame Γ P Q → Frame Δ P Q
renᶠ ρ □ = □
renᶠ ρ ([ 𝐸 ]· M) = [ renᶠ ρ 𝐸 ]· ren ρ M
renᶠ ρ (v ·[ 𝐸 ]) = ren-val ρ v ·[ renᶠ ρ 𝐸 ]
renᶠ ρ ([ 𝐸 ]⦅ f ⦆ M) = [ renᶠ ρ 𝐸 ]⦅ f ⦆ ren ρ M
renᶠ ρ (v ⦅ f ⦆[ 𝐸 ]) = ren-val ρ v ⦅ f ⦆[ renᶠ ρ 𝐸 ]
renᶠ ρ ([ 𝐸 ]⇑ g) = [ renᶠ ρ 𝐸 ]⇑ g
renᶠ ρ ([ 𝐸 ]＠⟨⟩ ±p) = [ renᶠ ρ 𝐸 ]＠⟨⟩ ±p
renᶠ ρ (″perform e∈E [ 𝐸 ] eq) = ″perform e∈E [ renᶠ ρ 𝐸 ] eq
renᶠ ρ (′handle H [ 𝐸 ]) = ′handle (renʰ ρ H) [ renᶠ ρ 𝐸 ]

liftᶠ : Frame Γ P Q → Frame (Γ ▷ A) P Q
liftᶠ = renᶠ S_

liftʰ : Γ ⊢ P ➡ Q → Γ ▷ A ⊢ P ➡ Q
liftʰ = renʰ S_
```
