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
  _·_ : Term → Term → Term
  fun : Var → Type → Term → Term
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

  _·_ : ∀ {E A B N M}
    →  Γ ⊢ N ⦂ ⟨ E ⟩ (A ⇒ ⟨ E ⟩ B)
    →  Γ ⊢ M ⦂ ⟨ E ⟩ A
       ---------------------------
    →  Γ ⊢ N · M ⦂ ⟨ E ⟩ B

  fun : ∀ {E F A B x M}
    →  Γ ▷ x ⦂ A ⊢ M ⦂ ⟨ E ⟩ B
       ------------------------
    →  Γ ⊢ fun x A M ⦂ ⟨ F ⟩ (A ⇒ ⟨ E ⟩ B)

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
open import Core using (∅; _▷_; _∋_; Z; S_; _⊢_; `_; _·_; ƛ_; perform-; cast)
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
⌊ N · M ⌋ = ⌊ N ⌋ · ⌊ M ⌋
⌊ fun M ⌋ = ƛ ⌊ M ⌋
⌊ perform- e∈E M eq ⌋ = perform- e∈E ⌊ M ⌋ eq
⌊ materialize Q≤P M ⌋ = cast (- Q≤P) ⌊ M ⌋
⌊ subsumption P⊑Q M ⌋ = cast (* P⊑Q) ⌊ M ⌋
```

```
infix 4 _≤ᵘ_ _≤ᵍ_ _∋_≤⦂_ _⊢_≤ᵈ_⦂_

data _≤ᵘ_ : Term → Term → Set where
  `_ : ∀ {x} → ` x ≤ᵘ ` x
  _·_ : ∀ {M M′ N N′} → N ≤ᵘ N′ → M ≤ᵘ M′ → N · M ≤ᵘ N′ · M′
  fun : ∀ {x A A′ M M′} → A ≤ A′ → M ≤ᵘ M′ → fun x A M ≤ᵘ fun x A′ M′
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

  _·_ : ∀ {E E′ A A′ B B′ N N′ M M′}
          {A⇒B≤ : (A ⇒ ⟨ E ⟩ B) ≤ (A′ ⇒ ⟨ E′ ⟩ B′)}
          (let E≤ = _≤ᶜ_.effects (cod A⇒B≤))
    →  Γ≤ ⊢ N ≤ᵈ N′ ⦂ ⟨ E≤ ⟩ A⇒B≤
    →  Γ≤ ⊢ M ≤ᵈ M′ ⦂ ⟨ E≤ ⟩ dom A⇒B≤
       -------------------------------------
    →  Γ≤ ⊢ N · M ≤ᵈ N′ · M′ ⦂ cod A⇒B≤


  fun : ∀ {E E′ A A′ P P′ x M M′}
          {E≤ : E ≤ᵉ E′} {A⇒P≤ : A ⇒ P ≤ A′ ⇒ P′}
    →  Γ≤ ▷ x ⦂ dom A⇒P≤ ⊢ M ≤ᵈ M′ ⦂ cod A⇒P≤
       ------------------------
    →  Γ≤ ⊢ fun x A M ≤ᵈ fun x A′ M′ ⦂ ⟨ E≤ ⟩ A⇒P≤

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
coarsen (N · M) (N≤ · M≤) = coarsen N N≤ · coarsen M M≤
coarsen (fun M) (fun A≤ M≤) = ≤materialize (left-idᶜ (⟨ id ⟩ (A≤ ⇒ ⟨ id ⟩ id))) (fun (coarsen M M≤))
coarsen (perform- x M x₁) (perform M≤) = {! !}
coarsen (materialize P≤Q M) M≤ = ≤materialize (left-idᶜ P≤Q) (materialize≤ refl (coarsen M M≤))
coarsen (subsumption Q⊑P M) M≤ = subsumption Q⊑P Q⊑P (coarsen M M≤)
```

```
halfˣ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {x} {A A′} {A≤ : A ≤ A′}
  →  Γ≤ ∋ x ≤⦂ A≤
  →  Γ ∋ x ⦂ A × Γ′ ∋ x ⦂ A′
halfˣ here = here , here
halfˣ (there x≢y X≤) with halfˣ X≤
... | X , X′ = there x≢y X , there x≢y X′

half : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {M M′} {P P′} {P≤ : P ≤ᶜ P′}
  →  Γ≤ ⊢ M ≤ᵈ M′ ⦂ P≤
  →  Γ ⊢ M ⦂ P × Γ′ ⊢ M′ ⦂ P′
half (` x≤) with halfˣ x≤
... | x , x′ = ` x , ` x′
half (N≤ · M≤) with half N≤ | half M≤
... | N , N′ | M , M′ = N · M , N′ · M′
half (fun M≤) with half M≤
... | M , M′ = fun M , fun M′
half (perform- e∈E e∈E′ M≤ eq) with half M≤
... | M , M′ = perform- e∈E M eq , perform- e∈E′ M′ eq
half (materialize≤ {Q≤P = Q≤P} comm M≤) with half M≤
... | M , M′ = materialize Q≤P M , M′
half (≤materialize {Q′≤P′ = Q′≤P′} comm M≤) with half M≤
... | M , M′ = M , materialize Q′≤P′ M′
half (subsumption P⊑Q P′⊑Q′ M≤) with half M≤
... | M , M′ = subsumption P⊑Q M , subsumption P′⊑Q′ M′
```

```
open import Prec
```

```
⌊_⌋≤ᵍ : ∀ {Γ Γ′} → Γ ≤ᵍ Γ′ → ⌊ Γ ⌋ᵍ ≤ᴳ ⌊ Γ′ ⌋ᵍ
⌊ ∅ ⌋≤ᵍ = ∅
⌊ Γ≤ ▷ x ⦂ A≤ ⌋≤ᵍ = ⌊ Γ≤ ⌋≤ᵍ ▷ A≤

⌊_⌋ᴹ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {M M′} {P P′} {P≤ : P ≤ᶜ P′}
  → (M≤ : Γ≤ ⊢ M ≤ᵈ M′ ⦂ P≤)
    (let M , M′ = half M≤)
  → ⌊ Γ≤ ⌋≤ᵍ ⊢ ⌊ M ⌋ ≤ᴹ ⌊ M′ ⌋ ⦂ P≤
⌊ ` x≤ ⌋ᴹ = `≤` ?
⌊ _·_ {A⇒B≤ = A⇒B≤} N≤ M≤ ⌋ᴹ = ·≤· {p = A⇒B≤} ? ?
⌊ fun M≤ ⌋ᴹ = ƛ≤ƛ ?
⌊ perform- x x₁ x₂ eq ⌋ᴹ = {! !}
⌊ materialize≤ comm M≤ ⌋ᴹ = cast≤ comm ⌊ M≤ ⌋ᴹ
⌊ ≤materialize comm M≤ ⌋ᴹ = ≤cast comm ⌊ M≤ ⌋ᴹ
⌊ subsumption x x₁ x₂ ⌋ᴹ = {! !}
```
