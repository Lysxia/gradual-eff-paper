## Surface syntax

```
module Surface where

open import Data.String using (String)
open import Utils
open import Type
```

```
Var : Set
Var = String

data Term : Set where
  `_ : Var -> Term
  fun : Var → Type → Term → Term
  _·_ : Term → Term → Term
  $_ : ∀ {ι} → rep ι → Term
  _⦅_⦆_ : ∀ {ι ι′ ι″} → Term → (rep ι → rep ι′ → rep ι″) → Term → Term
  perform : Op → Term → Term
```

```
infixl 5 _▷_⦂_

data Context : Set where
  ∅ : Context
  _▷_⦂_ : Context → Var → Type → Context
```

```
infixl 4 _∋_⦂_

data _∋_⦂_ : Context → Var → Type → Set where
  here : ∀ {Γ x A} → Γ ▷ x ⦂ A ∋ x ⦂ A
  there : ∀ {Γ x y A B} → x ≢ y → Γ ∋ x ⦂ A → Γ ▷ y ⦂ B ∋ x ⦂ A
```

```
infixl 4 _⊢_⦂_

data _⊢_⦂_ (Γ : Context) : Term → Typeᶜ → Set where
  `_ : ∀ {E A x}
    →  Γ ∋ x ⦂ A
       -----------------
    →  Γ ⊢ ` x ⦂ ⟨ E ⟩ A

  fun : ∀ {E F A B x M}
    →  Γ ▷ x ⦂ A ⊢ M ⦂ ⟨ E ⟩ B
       ------------------------
    →  Γ ⊢ fun x A M ⦂ ⟨ F ⟩ (A ⇒ ⟨ E ⟩ B)

  _·_ : ∀ {E A B N M}
    →  Γ ⊢ N ⦂ ⟨ E ⟩ (A ⇒ ⟨ E ⟩ B)
    →  Γ ⊢ M ⦂ ⟨ E ⟩ A
       ---------------------------
    →  Γ ⊢ N · M ⦂ ⟨ E ⟩ B

  $_ : ∀ {E ι}
    →  (κ : rep ι)
       -------------
    →  Γ ⊢ $ κ ⦂ ⟨ E ⟩ $ ι

  _⦅_⦆_ : ∀ {E ι ι′ ι″ M N}
    →  Γ ⊢ M ⦂ ⟨ E ⟩ $ ι
    →  (f : rep ι → rep ι′ → rep ι″)
    →  Γ ⊢ N ⦂ ⟨ E ⟩ $ ι′
       ------------------
    →  Γ ⊢ M ⦅ f ⦆ N ⦂ ⟨ E ⟩ $ ι″

  perform- : ∀ {e E A M}
    →  e ∈☆ E
    →  Γ ⊢ M ⦂ ⟨ E ⟩ request e
    →  response e ≡ A
       -----------------------
    →  Γ ⊢ perform e M ⦂ ⟨ E ⟩ A

  materialize : ∀ {P Q M}
    →  Q ≤ᶜ P
    →  Γ ⊢ M ⦂ P
       ------------
    →  Γ ⊢ M ⦂ Q

  subsumption : ∀ {P Q M}
    →  P ⊑ᶜ Q
    →  Γ ⊢ M ⦂ P
       ---------
    →  Γ ⊢ M ⦂ Q
```

```
open import Core using (∅; _▷_; _∋_; Z; S_; _⊢_; `_; _·_; ƛ_; $_; _⦅_⦆_; perform-; cast)
```

```
⌊_⌋ᵍ : Context → Core.Context
⌊ ∅ ⌋ᵍ = ∅
⌊ Γ ▷ _ ⦂ A ⌋ᵍ = ⌊ Γ ⌋ᵍ ▷ A
```

```
⌊_⌋ˣ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ⌊ Γ ⌋ᵍ ∋ A
⌊ here ⌋ˣ = Z
⌊ there _ x ⌋ˣ = S ⌊ x ⌋ˣ
```

```
⌊_⌋ : ∀ {Γ M P} → Γ ⊢ M ⦂ P → ⌊ Γ ⌋ᵍ ⊢ P
⌊ ` x ⌋ = ` ⌊ x ⌋ˣ
⌊ fun M ⌋ = ƛ ⌊ M ⌋
⌊ N · M ⌋ = ⌊ N ⌋ · ⌊ M ⌋
⌊ $ κ ⌋ = $ κ
⌊ M ⦅ f ⦆ N ⌋ = ⌊ M ⌋ ⦅ f ⦆ ⌊ N ⌋
⌊ perform- e∈E M eq ⌋ = perform- e∈E ⌊ M ⌋ eq
⌊ materialize Q≤P M ⌋ = cast (- Q≤P) ⌊ M ⌋
⌊ subsumption P⊑Q M ⌋ = cast (* P⊑Q) ⌊ M ⌋
```

```
infix 4 _≤ᵘ_ _≤ᵍ_ _∋_≤⦂_ _⊢_≤ᵈ_⦂_

data _≤ᵘ_ : Term → Term → Set where
  `_ : ∀ {x} → ` x ≤ᵘ ` x
  fun : ∀ {x A A′ M M′} → A ≤ A′ → M ≤ᵘ M′ → fun x A M ≤ᵘ fun x A′ M′
  _·_ : ∀ {M M′ N N′} → N ≤ᵘ N′ → M ≤ᵘ M′ → N · M ≤ᵘ N′ · M′
  $_ : ∀ {ι} (κ : rep ι) → $ κ ≤ᵘ $ κ
  _⦅_⦆_ : ∀ {ι ι′ ι″ M M′ N N′} → M ≤ᵘ M′ → (f : rep ι → rep ι′ → rep ι″) → N ≤ᵘ N′ → M ⦅ f ⦆ N ≤ᵘ M′ ⦅ f ⦆ N′
  perform : ∀ {e M M′} → M ≤ᵘ M′ → perform e M ≤ᵘ perform e M′
```

```
data _≤ᵍ_ : Context → Context → Set where
  ∅ : ∅ ≤ᵍ ∅
  _▷_⦂_ : ∀ {Γ Γ′} → Γ ≤ᵍ Γ′ → ∀ x {A A′} → A ≤ A′ → Γ ▷ x ⦂ A ≤ᵍ Γ′ ▷ x ⦂ A′
```

```
data _∋_≤⦂_ : ∀ {Γ Γ′} (Γ≤ : Γ ≤ᵍ Γ′) x {A A′} → A ≤ A′ → Set where
  there : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {x y A A′} {A≤ : A ≤ A′} {B B′} {B≤ : B ≤ B′}
    →   (neq : x ≢ y)
    →   Γ≤ ∋ x ≤⦂ A≤
    →   Γ≤ ▷ y ⦂ B≤ ∋ x ≤⦂ A≤

  here : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {x A A′} {A≤ : A ≤ A′}
    →   Γ≤ ▷ x ⦂ A≤ ∋ x ≤⦂ A≤
```

```
data _⊢_≤ᵈ_⦂_ {Γ Γ′} (Γ≤ : Γ ≤ᵍ Γ′) : Term → Term → ∀ {P P′} → P ≤ᶜ P′ → Set where
  `_ : ∀ {x E E′ A A′} {X : Γ ∋ x ⦂ A} {X′ : Γ′ ∋ x ⦂ A′}
    →  {A≤ : A ≤ A′}
    →  {E≤ : E ≤ᵉ E′}
    →  Γ≤ ∋ x ≤⦂ A≤
       ---------------------------
    →  Γ≤ ⊢ ` x ≤ᵈ ` x ⦂ ⟨ E≤ ⟩ A≤

  fun : ∀ {E E′ A A′ P P′ x M M′}
          {E≤ : E ≤ᵉ E′} {A⇒P≤ : A ⇒ P ≤ A′ ⇒ P′}
    →  Γ≤ ▷ x ⦂ dom A⇒P≤ ⊢ M ≤ᵈ M′ ⦂ cod A⇒P≤
       ------------------------
    →  Γ≤ ⊢ fun x A M ≤ᵈ fun x A′ M′ ⦂ ⟨ E≤ ⟩ A⇒P≤

  _·_ : ∀ {E E′ A A′ B B′ N N′ M M′}
          {A⇒B≤ : (A ⇒ ⟨ E ⟩ B) ≤ (A′ ⇒ ⟨ E′ ⟩ B′)}
          (let E≤ = _≤ᶜ_.effects (cod A⇒B≤))
    →  Γ≤ ⊢ N ≤ᵈ N′ ⦂ ⟨ E≤ ⟩ A⇒B≤
    →  Γ≤ ⊢ M ≤ᵈ M′ ⦂ ⟨ E≤ ⟩ dom A⇒B≤
       -------------------------------------
    →  Γ≤ ⊢ N · M ≤ᵈ N′ · M′ ⦂ cod A⇒B≤

  $_ : ∀ {E E′ ι} {E≤ : E ≤ᵉ E′}
    →  (κ : rep ι)
       ---------------------------
    →  Γ≤ ⊢ $ κ ≤ᵈ $ κ ⦂ ⟨ E≤ ⟩ id {A = $ ι}

  _⦅_⦆_ : ∀ {E E′ ι ι′ ι″ M M′ N N′} {E≤ : E ≤ᵉ E′}
    →  Γ≤ ⊢ M ≤ᵈ M′ ⦂ ⟨ E≤ ⟩ id {A = $ ι}
    →  (f : rep ι → rep ι′ → rep ι″)
    →  Γ≤ ⊢ N ≤ᵈ N′ ⦂ ⟨ E≤ ⟩ id {A = $ ι′}
       ---------------------------
    →  Γ≤ ⊢ M ⦅ f ⦆ N ≤ᵈ M′ ⦅ f ⦆ N′ ⦂ ⟨ E≤ ⟩ id {A = $ ι″}

  perform- : ∀ {e E E′ A M M′}
               {E≤ : E ≤ᵉ E′}
    →  e ∈☆ E
    →  e ∈☆ E′
    →  Γ≤ ⊢ M ≤ᵈ M′ ⦂ ⟨ E≤ ⟩ (id {A = request e})
    →  (eq : response e ≡ A)
       -----------------------
    →  Γ≤ ⊢ perform e M ≤ᵈ perform e M′ ⦂ ⟨ E≤ ⟩ (id {A = A})

  materialize≤ : ∀ {P P′ Q M M′}
                  {P≤ : P ≤ᶜ P′} {Q≤ : Q ≤ᶜ P′}
    →  {Q≤P : Q ≤ᶜ P}
    →  Q≤P ⨟ᶜ P≤ ≡ Q≤
    →  Γ≤ ⊢ M ≤ᵈ M′ ⦂ P≤
       ------------
    →  Γ≤ ⊢ M ≤ᵈ M′ ⦂ Q≤

  ≤materialize : ∀ {P P′ Q′ M M′}
                  {P≤ : P ≤ᶜ P′} {Q≤ : P ≤ᶜ Q′}
    →  {Q′≤P′ : Q′ ≤ᶜ P′}
    →  Q≤ ⨟ᶜ Q′≤P′ ≡ P≤
    →  Γ≤ ⊢ M ≤ᵈ M′ ⦂ P≤
       ------------
    →  Γ≤ ⊢ M ≤ᵈ M′ ⦂ Q≤

  subsumption : ∀ {P P′ Q Q′ M M′}
                  {P≤ : P ≤ᶜ P′} {Q≤ : Q ≤ᶜ Q′}
    → P ⊑ᶜ Q
    → P′ ⊑ᶜ Q′
    → Γ≤ ⊢ M ≤ᵈ M′ ⦂ P≤
      -----------------
    → Γ≤ ⊢ M ≤ᵈ M′ ⦂ Q≤
```

```
≤ᶜ-refl : ∀ {P} → P ≤ᶜ P
≤ᶜ-refl = ⟨ id ⟩ id
```

```
coarsen : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {M M′} {P}
  → Γ ⊢ M ⦂ P
  → M ≤ᵘ M′
  → Γ≤ ⊢ M ≤ᵈ M′ ⦂ ⟨ id ⟩ id
coarsen (` x) `_ = {! !}
coarsen (fun M) (fun A≤ M≤) = ≤materialize (left-idᶜ (⟨ id ⟩ (A≤ ⇒ ⟨ id ⟩ id))) (fun (coarsen M M≤))
coarsen (N · M) (N≤ · M≤) = coarsen N N≤ · coarsen M M≤
coarsen ($ .κ) ($ κ) = $ κ
coarsen (M ⦅ .f ⦆ N) (M≤ ⦅ f ⦆ N≤) = coarsen M M≤ ⦅ f ⦆ coarsen N N≤
coarsen (perform- x M x₁) (perform M≤) = {! !}
coarsen (materialize P≤Q M) M≤ = ≤materialize (left-idᶜ P≤Q) (materialize≤ refl (coarsen M M≤))
coarsen (subsumption Q⊑P M) M≤ = subsumption Q⊑P Q⊑P (coarsen M M≤)
```

```
leftˣ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {x} {A A′} {A≤ : A ≤ A′}
  →  Γ≤ ∋ x ≤⦂ A≤
  →  Γ ∋ x ⦂ A
leftˣ here = here
leftˣ (there x≢y X≤) = there x≢y (leftˣ X≤)

left : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {M M′} {P P′} {P≤ : P ≤ᶜ P′}
  →  Γ≤ ⊢ M ≤ᵈ M′ ⦂ P≤
  →  Γ ⊢ M ⦂ P
left (` x≤) = ` leftˣ x≤
left (N≤ · M≤) = left N≤ · left M≤
left (fun M≤) = fun (left M≤)
left ($ κ) = $ κ
left (M≤ ⦅ f ⦆ N≤) = left M≤ ⦅ f ⦆ left N≤
left (perform- e∈E e∈E′ M≤ eq) = perform- e∈E (left M≤) eq
left (materialize≤ {Q≤P = Q≤P} comm M≤) = materialize Q≤P (left M≤)
left (≤materialize {Q′≤P′ = Q′≤P′} comm M≤) = left M≤
left (subsumption P⊑Q P′⊑Q′ M≤) = subsumption P⊑Q (left M≤)
```

```
rightˣ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {x} {A A′} {A≤ : A ≤ A′}
  →  Γ≤ ∋ x ≤⦂ A≤
  →  Γ′ ∋ x ⦂ A′
rightˣ here = here
rightˣ (there x≢y X≤) = there x≢y (rightˣ X≤)

right : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {M M′} {P P′} {P≤ : P ≤ᶜ P′}
  →  Γ≤ ⊢ M ≤ᵈ M′ ⦂ P≤
  →  Γ′ ⊢ M′ ⦂ P′
right (` x≤) = ` rightˣ x≤
right (N≤ · M≤) = right N≤ · right M≤
right (fun M≤) = fun (right M≤)
right ($ κ) = $ κ
right (M≤ ⦅ f ⦆ N≤) = right M≤ ⦅ f ⦆ right N≤
right (perform- e∈E e∈E′ M≤ eq) = perform- e∈E′ (right M≤) eq
right (materialize≤ {Q≤P = Q≤P} comm M≤) = right M≤
right (≤materialize {Q′≤P′ = Q′≤P′} comm M≤) = materialize Q′≤P′ (right M≤)
right (subsumption P⊑Q P′⊑Q′ M≤) = subsumption P′⊑Q′ (right M≤)
```

```
open import Prec
```

```
⌊_⌋≤ᵍ : ∀ {Γ Γ′} → Γ ≤ᵍ Γ′ → ⌊ Γ ⌋ᵍ ≤ᴳ ⌊ Γ′ ⌋ᵍ
⌊ ∅ ⌋≤ᵍ = ∅
⌊ Γ≤ ▷ x ⦂ A≤ ⌋≤ᵍ = ⌊ Γ≤ ⌋≤ᵍ ▷ A≤

⌊_⌋≤ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {M M′} {P P′} {P≤ : P ≤ᶜ P′}
  → (M≤ : Γ≤ ⊢ M ≤ᵈ M′ ⦂ P≤)
  → ⌊ Γ≤ ⌋≤ᵍ ⊢ ⌊ left M≤ ⌋ ≤ᴹ ⌊ right M≤ ⌋ ⦂ P≤
⌊ ` x≤ ⌋≤ = `≤` ?
⌊ fun M≤ ⌋≤ = ƛ≤ƛ ?
⌊ _·_ {A⇒B≤ = A⇒B≤} N≤ M≤ ⌋≤ = ·≤· {p = A⇒B≤} ? ?
⌊ $ κ ⌋≤ = $≤$ κ
⌊ M ⦅ f ⦆ N ⌋≤ = ⦅⦆≤⦅⦆ f ⌊ M ⌋≤ ⌊ N ⌋≤
⌊ perform- x x₁ x₂ eq ⌋≤ = {! !}
⌊ materialize≤ comm M≤ ⌋≤ = cast≤ comm ⌊ M≤ ⌋≤
⌊ ≤materialize comm M≤ ⌋≤ = ≤cast comm ⌊ M≤ ⌋≤
⌊ subsumption x x₁ x₂ ⌋≤ = {! !}
```
