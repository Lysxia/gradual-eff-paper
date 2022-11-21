## Surface syntax

```
module Surface where

open import Data.String using (String)
open import Data.List.Base using (map)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise; []; _∷_)
open import Utils
open import Type
```

```
Var : Set
Var = String

data Term : Set
data Handler : Set

data Term where
  `_ : Var -> Term
  fun : Var → Type → Term → Term
  _·_ : Term → Term → Term
  $_ : ∀ {ι} → rep ι → Term
  _⦅_⦆_ : ∀ {ι ι′ ι″} → Term → (rep ι → rep ι′ → rep ι″) → Term → Term
  perform : Op → Term → Term
  handle : Handler → Term → Term

Untyped-Op-Clauses : Set
Untyped-Op-Clauses = List (Op × Var × Var × Term)

data Handler where
  handler : Var × Term → Untyped-Op-Clauses → Handler
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
infixl 4 _⊢_⦂_ _⊢_⦂_⇒ʰ_

data _⊢_⦂_ (Γ : Context) : Term → Typeᶜ → Set
data _⊢_⦂_⇒ʰ_ (Γ : Context) : Handler → Typeᶜ → Typeᶜ → Set

data _⊢_⦂_ Γ where
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

  handle : ∀ {H M P Q}
    →  Γ ⊢ H ⦂ P ⇒ʰ Q
    →  Γ ⊢ M ⦂ P
    →  Γ ⊢ handle H M ⦂ Q

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
Op-Clauses : Context → Typeᶜ → List (Op × Var × Var × Term) → Set
Op-Clauses Γ Q Ns
  = All (λ{ (e , x , k , N) → Γ ▷ x ⦂ request e ▷ k ⦂ (response e ⇒ Q) ⊢ N ⦂ Q }) Ns

data _⊢_⦂_⇒ʰ_ Γ where
  handler : ∀ {x E A F B M Ns}
    →  E ≡ map proj₁ Ns ++☆ F
    →  Γ ▷ x ⦂ A ⊢ M ⦂ ⟨ F ⟩ B
    →  Op-Clauses Γ (⟨ F ⟩ B) Ns
    →  Γ ⊢ handler (x , M) Ns ⦂ ⟨ E ⟩ A ⇒ʰ ⟨ F ⟩ B
```

```
open import Core using (∅; _▷_; _∋_; Z; S_; _⊢_; `_; _·_; ƛ_; $_; _⦅_⦆_; perform-; cast; handle; _⊢_⇒ʰ_)
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
⌊ handle H M ⌋ = handle ⌊ H ⌋ʰ ⌊ M ⌋
  where
    ⌊_⌋ᵒ : ∀ {Γ Q Ns} → Op-Clauses Γ Q Ns → Core.On-Perform ⌊ Γ ⌋ᵍ Q (map proj₁ Ns)
    ⌊ [] ⌋ᵒ = []
    ⌊ N ∷ Ns ⌋ᵒ = ⌊ N ⌋ ∷ ⌊ Ns ⌋ᵒ

    ⌊_⌋ʰ : ∀ {Γ H P Q} → Γ ⊢ H ⦂ P ⇒ʰ Q → ⌊ Γ ⌋ᵍ ⊢ P ⇒ʰ Q
    ⌊ handler eq M Ns ⌋ʰ = record
      { Hooks-handled = eq
      ; on-return = ⌊ M ⌋
      ; on-perform = ⌊ Ns ⌋ᵒ
      }
⌊ materialize Q≤P M ⌋ = cast (- Q≤P) ⌊ M ⌋
⌊ subsumption P⊑Q M ⌋ = cast (* P⊑Q) ⌊ M ⌋
```

```
infix 4 _≤ᵘ_ _≤ᵍ_ _∋_≤⦂_

data _≤ᵘ_ : Term → Term → Set
data _≤ʰ_ : Handler → Handler → Set

data _≤ᵘ_ where
  `_ : ∀ {x} → ` x ≤ᵘ ` x
  fun : ∀ {x A A′ M M′} → A ≤ A′ → M ≤ᵘ M′ → fun x A M ≤ᵘ fun x A′ M′
  _·_ : ∀ {M M′ N N′} → N ≤ᵘ N′ → M ≤ᵘ M′ → N · M ≤ᵘ N′ · M′
  $_ : ∀ {ι} (κ : rep ι) → $ κ ≤ᵘ $ κ
  _⦅_⦆_ : ∀ {ι ι′ ι″ M M′ N N′} → M ≤ᵘ M′ → (f : rep ι → rep ι′ → rep ι″) → N ≤ᵘ N′ → M ⦅ f ⦆ N ≤ᵘ M′ ⦅ f ⦆ N′
  perform : ∀ {e M M′} → M ≤ᵘ M′ → perform e M ≤ᵘ perform e M′
  handle : ∀ {H H′ M M′} → H ≤ʰ H′ → M ≤ᵘ M′ → handle H M ≤ᵘ handle H′ M′

_≤ᵒ_ : Untyped-Op-Clauses → Untyped-Op-Clauses → Set
_≤ᵒ_ = Pointwise (λ{ (e , x , k , N) (e′ , x′ , k′ , N′) → e ≡ e′ × x ≡ x′ × k ≡ k′ × N ≤ᵘ N′ })

data _≤ʰ_ where
  handler : ∀ {x M M′ Ns Ns′}
    →  M ≤ᵘ M′
    →  Ns ≤ᵒ Ns′
    →  handler (x , M) Ns ≤ʰ handler (x , M′) Ns′
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
infix 4 _⊢_≤ᵗ_⦂_ _⊢_≤ᵗ_⦂_⇒ʰ_

data _⊢_≤ᵗ_⦂_ {Γ Γ′} (Γ≤ : Γ ≤ᵍ Γ′) : Term → Term → ∀ {P P′} → P ≤ᶜ P′ → Set
data _⊢_≤ᵗ_⦂_⇒ʰ_ {Γ Γ′} (Γ≤ : Γ ≤ᵍ Γ′) : Handler → Handler → ∀ {P P′ Q Q′} → P ≤ᶜ P′ → Q ≤ᶜ Q′ → Set

data _⊢_≤ᵗ_⦂_ {Γ Γ′} Γ≤ where
  `_ : ∀ {x E E′ A A′} {X : Γ ∋ x ⦂ A} {X′ : Γ′ ∋ x ⦂ A′}
    →  {A≤ : A ≤ A′}
    →  {E≤ : E ≤ᵉ E′}
    →  Γ≤ ∋ x ≤⦂ A≤
       ---------------------------
    →  Γ≤ ⊢ ` x ≤ᵗ ` x ⦂ ⟨ E≤ ⟩ A≤

  fun : ∀ {E E′ A A′ P P′ x M M′}
          {E≤ : E ≤ᵉ E′} {A⇒P≤ : A ⇒ P ≤ A′ ⇒ P′}
    →  Γ≤ ▷ x ⦂ dom A⇒P≤ ⊢ M ≤ᵗ M′ ⦂ cod A⇒P≤
       ------------------------
    →  Γ≤ ⊢ fun x A M ≤ᵗ fun x A′ M′ ⦂ ⟨ E≤ ⟩ A⇒P≤

  _·_ : ∀ {E E′ A A′ B B′ N N′ M M′}
          {A⇒B≤ : (A ⇒ ⟨ E ⟩ B) ≤ (A′ ⇒ ⟨ E′ ⟩ B′)}
          (let E≤ = _≤ᶜ_.effects (cod A⇒B≤))
    →  Γ≤ ⊢ N ≤ᵗ N′ ⦂ ⟨ E≤ ⟩ A⇒B≤
    →  Γ≤ ⊢ M ≤ᵗ M′ ⦂ ⟨ E≤ ⟩ dom A⇒B≤
       -------------------------------------
    →  Γ≤ ⊢ N · M ≤ᵗ N′ · M′ ⦂ cod A⇒B≤

  $_ : ∀ {E E′ ι} {E≤ : E ≤ᵉ E′}
    →  (κ : rep ι)
       ---------------------------
    →  Γ≤ ⊢ $ κ ≤ᵗ $ κ ⦂ ⟨ E≤ ⟩ id {A = $ ι}

  _⦅_⦆_ : ∀ {E E′ ι ι′ ι″ M M′ N N′} {E≤ : E ≤ᵉ E′}
    →  Γ≤ ⊢ M ≤ᵗ M′ ⦂ ⟨ E≤ ⟩ id {A = $ ι}
    →  (f : rep ι → rep ι′ → rep ι″)
    →  Γ≤ ⊢ N ≤ᵗ N′ ⦂ ⟨ E≤ ⟩ id {A = $ ι′}
       ---------------------------
    →  Γ≤ ⊢ M ⦅ f ⦆ N ≤ᵗ M′ ⦅ f ⦆ N′ ⦂ ⟨ E≤ ⟩ id {A = $ ι″}

  perform- : ∀ {e E E′ A M M′}
               {E≤ : E ≤ᵉ E′}
    →  e ∈☆ E
    →  e ∈☆ E′
    →  Γ≤ ⊢ M ≤ᵗ M′ ⦂ ⟨ E≤ ⟩ (id {A = request e})
    →  (eq : response e ≡ A)
       -----------------------
    →  Γ≤ ⊢ perform e M ≤ᵗ perform e M′ ⦂ ⟨ E≤ ⟩ (id {A = A})

  handle : ∀ {P P′ Q Q′} {P≤ : P ≤ᶜ P′} {Q≤ : Q ≤ᶜ Q′} {H H′ M M′}
    →  Γ≤ ⊢ H ≤ᵗ H′ ⦂ P≤ ⇒ʰ Q≤
    →  Γ≤ ⊢ M ≤ᵗ M′ ⦂ P≤
       -----------------------------------
    →  Γ≤ ⊢ handle H M ≤ᵗ handle H′ M′ ⦂ Q≤

  materialize≤ : ∀ {P P′ Q M M′}
                  {P≤ : P ≤ᶜ P′} {Q≤ : Q ≤ᶜ P′}
    →  {Q≤P : Q ≤ᶜ P}
    →  Q≤P ⨟ᶜ P≤ ≡ Q≤
    →  Γ≤ ⊢ M ≤ᵗ M′ ⦂ P≤
       ------------
    →  Γ≤ ⊢ M ≤ᵗ M′ ⦂ Q≤

  ≤materialize : ∀ {P P′ Q′ M M′}
                  {P≤ : P ≤ᶜ P′} {Q≤ : P ≤ᶜ Q′}
    →  {Q′≤P′ : Q′ ≤ᶜ P′}
    →  Q≤ ⨟ᶜ Q′≤P′ ≡ P≤
    →  Γ≤ ⊢ M ≤ᵗ M′ ⦂ P≤
       ------------
    →  Γ≤ ⊢ M ≤ᵗ M′ ⦂ Q≤

  subsumption : ∀ {P P′ Q Q′ M M′}
                  {P≤ : P ≤ᶜ P′} {Q≤ : Q ≤ᶜ Q′}
    → P ⊑ᶜ Q
    → P′ ⊑ᶜ Q′
    → Γ≤ ⊢ M ≤ᵗ M′ ⦂ P≤
      -----------------
    → Γ≤ ⊢ M ≤ᵗ M′ ⦂ Q≤

data _⊢_≤ᵗ_⦂_⇒ʰ_ {Γ Γ′} Γ≤ where
  handler : ∀ {E E′ F F′ A A′ B B′ x M M′ Ns Ns′}
              {E≤ : E ≤ᵉ E′} {F≤ : F ≤ᵉ F′} {A≤ : A ≤ A′} {B≤ : B ≤ B′}
    →  Γ≤ ▷ x ⦂ A≤ ⊢ M ≤ᵗ M′ ⦂ ⟨ F≤ ⟩ B≤
    →  Γ≤ ⊢ handler (x , M) Ns ≤ᵗ handler (x , M′) Ns′ ⦂ ⟨ E≤ ⟩ A≤ ⇒ʰ ⟨ F≤ ⟩ B≤
```

```
≤ᶜ-refl : ∀ {P} → P ≤ᶜ P
≤ᶜ-refl = ⟨ id ⟩ id
```

```
open import Prec
```

```
coarsenˣ : ∀ {Γ Γ′} (Γ≤ : Γ ≤ᵍ Γ′) {x A}
  → Γ ∋ x ⦂ A
  → ∃[ A′ ] A ≤ A′ × Γ′ ∋ x ⦂ A′
coarsenˣ = ?
```

```
map-proj₁-≤ᵒ : ∀ {Ns Ns′} → Ns ≤ᵒ Ns′ → map proj₁ Ns ≡ map proj₁ Ns′
map-proj₁-≤ᵒ [] = refl
map-proj₁-≤ᵒ ((refl , _) ∷ Ns≤) rewrite map-proj₁-≤ᵒ Ns≤ = refl
```

```
coarsen : ∀ {Γ Γ′} (Γ≤ : Γ ≤ᵍ Γ′) {M M′} {P}
  → Γ ⊢ M ⦂ P
  → M ≤ᵘ M′
  → Γ′ ⊢ M′ ⦂ P
coarsen Γ≤ (` X) `_ with coarsenˣ Γ≤ X
... | A′ , A≤ , X′ = materialize (⟨ id ⟩ A≤) (` X′)
coarsen Γ≤ (fun M) (fun A≤ M≤) = materialize (⟨ id ⟩ (A≤ ⇒ ⟨ id ⟩ id)) (fun (coarsen (Γ≤ ▷ _ ⦂ A≤) M M≤))
coarsen Γ≤ (N · M) (N≤ · M≤) = coarsen Γ≤ N N≤ · coarsen Γ≤ M M≤
coarsen Γ≤ ($ .κ) ($ κ) = $ κ
coarsen Γ≤ (M ⦅ .f ⦆ N) (M≤ ⦅ f ⦆ N≤) = coarsen Γ≤ M M≤ ⦅ f ⦆ coarsen Γ≤ N N≤
coarsen Γ≤ (perform- x∈E ⊢M eq) (perform M≤) = perform- x∈E (coarsen Γ≤ ⊢M M≤) eq
coarsen Γ≤ (handle ⊢H ⊢M) (handle H≤ M≤) = handle (coarsenʰ Γ≤ ⊢H H≤) (coarsen Γ≤ ⊢M M≤)
  where
    coarsenʰ : ∀ {Γ Γ′} (Γ≤ : Γ ≤ᵍ Γ′) {H H′} {P Q}
      →  Γ ⊢ H ⦂ P ⇒ʰ Q
      →  H ≤ʰ H′
      →  Γ′ ⊢ H′ ⦂ P ⇒ʰ Q

    coarsenᵒ : ∀ {Γ Γ′} (Γ≤ : Γ ≤ᵍ Γ′) {Ns Ns′} {Q}
      →  Op-Clauses Γ Q Ns
      →  Ns ≤ᵒ Ns′
      →  Op-Clauses Γ′ Q Ns′
    coarsenᵒ Γ≤ [] [] = []
    coarsenᵒ Γ≤ (⊢N ∷ ⊢Ns) ((refl , refl , refl , N≤) ∷ Ns≤)
      = coarsen (Γ≤ ▷ _ ⦂ id ▷ _ ⦂ id) ⊢N N≤ ∷ coarsenᵒ Γ≤ ⊢Ns Ns≤

    coarsenʰ Γ≤ (handler eq ⊢M ⊢Ns) (handler M≤ Ns≤) rewrite map-proj₁-≤ᵒ Ns≤
      = handler eq (coarsen (Γ≤ ▷ _ ⦂ id) ⊢M M≤) (coarsenᵒ Γ≤ ⊢Ns Ns≤)
coarsen Γ≤ (materialize P≤Q ⊢M) M≤ = materialize P≤Q (coarsen Γ≤ ⊢M M≤)
coarsen Γ≤ (subsumption Q⊑P ⊢M) M≤ = subsumption Q⊑P (coarsen Γ≤ ⊢M M≤)
```

```
⌊_⌋≤ᵍ : ∀ {Γ Γ′} → Γ ≤ᵍ Γ′ → ⌊ Γ ⌋ᵍ ≤ᴳ ⌊ Γ′ ⌋ᵍ
⌊ ∅ ⌋≤ᵍ = ∅
⌊ Γ≤ ▷ x ⦂ A≤ ⌋≤ᵍ = ⌊ Γ≤ ⌋≤ᵍ ▷ A≤
```

```
≤coarsen : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {M M′} {P}
  →  (⊢M : Γ ⊢ M ⦂ P)
  →  (M≤ : M ≤ᵘ M′)
  →  ⌊ Γ≤ ⌋≤ᵍ ⊢ ⌊ ⊢M ⌋ ≤ᴹ ⌊ coarsen Γ≤ ⊢M M≤ ⌋ ⦂ ⟨ id ⟩ id
≤coarsen (` x) `_ = {! !}
≤coarsen (fun ⊢M) (fun x M≤) = ≤cast (left-idᶜ _) (ƛ≤ƛ (≤coarsen ⊢M M≤))
≤coarsen (⊢N · ⊢M) (N≤ · M≤) = ·≤· (≤coarsen ⊢N N≤) (≤coarsen ⊢M M≤)
≤coarsen ($ κ) ($ .κ) = $≤$ κ
≤coarsen (⊢M ⦅ f ⦆ ⊢N) (M≤ ⦅ .f ⦆ N≤) = ⦅⦆≤⦅⦆ f (≤coarsen ⊢M M≤) (≤coarsen ⊢N N≤)
≤coarsen (perform- e∈E ⊢M eq) (perform M≤) = perform≤perform (≤coarsen ⊢M M≤)
≤coarsen (handle ⊢H ⊢M) (handle H≤ M≤) = handle≤handle ? (≤coarsen ⊢M M≤)
≤coarsen (materialize P≤ ⊢M) M≤ = ≤cast (left-idᶜ _) (cast≤ refl (≤coarsen ⊢M M≤))
≤coarsen (subsumption P⊑ ⊢M) M≤ = *≤* (≤coarsen ⊢M M≤)
```

--  ⌊ Γ≤ ⌋≤ᵍ ⊢ ⌊ ⊢M ⌋ ≤ᴹ ⌊ ⊢M′ ⌋ ⦂ ⟨ id ⟩ id
-- ```
-- leftˣ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {x} {A A′} {A≤ : A ≤ A′}
--   →  Γ≤ ∋ x ≤⦂ A≤
--   →  Γ ∋ x ⦂ A
-- leftˣ here = here
-- leftˣ (there x≢y X≤) = there x≢y (leftˣ X≤)
--
-- left : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {M M′} {P P′} {P≤ : P ≤ᶜ P′}
--   →  Γ≤ ⊢ M ≤ᵗ M′ ⦂ P≤
--   →  Γ ⊢ M ⦂ P
-- left (` x≤) = ` leftˣ x≤
-- left (N≤ · M≤) = left N≤ · left M≤
-- left (fun M≤) = fun (left M≤)
-- left ($ κ) = $ κ
-- left (M≤ ⦅ f ⦆ N≤) = left M≤ ⦅ f ⦆ left N≤
-- left (perform- e∈E e∈E′ M≤ eq) = perform- e∈E (left M≤) eq
-- left (materialize≤ {Q≤P = Q≤P} comm M≤) = materialize Q≤P (left M≤)
-- left (≤materialize {Q′≤P′ = Q′≤P′} comm M≤) = left M≤
-- left (subsumption P⊑Q P′⊑Q′ M≤) = subsumption P⊑Q (left M≤)
-- ```
--
-- ```
-- rightˣ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {x} {A A′} {A≤ : A ≤ A′}
--   →  Γ≤ ∋ x ≤⦂ A≤
--   →  Γ′ ∋ x ⦂ A′
-- rightˣ here = here
-- rightˣ (there x≢y X≤) = there x≢y (rightˣ X≤)
--
-- right : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {M M′} {P P′} {P≤ : P ≤ᶜ P′}
--   →  Γ≤ ⊢ M ≤ᵗ M′ ⦂ P≤
--   →  Γ′ ⊢ M′ ⦂ P′
-- right (` x≤) = ` rightˣ x≤
-- right (N≤ · M≤) = right N≤ · right M≤
-- right (fun M≤) = fun (right M≤)
-- right ($ κ) = $ κ
-- right (M≤ ⦅ f ⦆ N≤) = right M≤ ⦅ f ⦆ right N≤
-- right (perform- e∈E e∈E′ M≤ eq) = perform- e∈E′ (right M≤) eq
-- right (materialize≤ {Q≤P = Q≤P} comm M≤) = right M≤
-- right (≤materialize {Q′≤P′ = Q′≤P′} comm M≤) = materialize Q′≤P′ (right M≤)
-- right (subsumption P⊑Q P′⊑Q′ M≤) = subsumption P′⊑Q′ (right M≤)
-- ```
--
--
--
-- ⌊_⌋≤ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᵍ Γ′} {M M′} {P P′} {P≤ : P ≤ᶜ P′}
--   → (M≤ : Γ≤ ⊢ M ≤ᵗ M′ ⦂ P≤)
--   → ⌊ Γ≤ ⌋≤ᵍ ⊢ ⌊ left M≤ ⌋ ≤ᴹ ⌊ right M≤ ⌋ ⦂ P≤
-- ⌊ ` x≤ ⌋≤ = `≤` ?
-- ⌊ fun M≤ ⌋≤ = ƛ≤ƛ ?
-- ⌊ _·_ {A⇒B≤ = A⇒B≤} N≤ M≤ ⌋≤ = ·≤· {p = A⇒B≤} ? ?
-- ⌊ $ κ ⌋≤ = $≤$ κ
-- ⌊ M ⦅ f ⦆ N ⌋≤ = ⦅⦆≤⦅⦆ f ⌊ M ⌋≤ ⌊ N ⌋≤
-- ⌊ perform- x x₁ x₂ eq ⌋≤ = {! !}
-- ⌊ materialize≤ comm M≤ ⌋≤ = cast≤ comm ⌊ M≤ ⌋≤
-- ⌊ ≤materialize comm M≤ ⌋≤ = ≤cast comm ⌊ M≤ ⌋≤
-- ⌊ subsumption x x₁ x₂ ⌋≤ = {! !}
-- ```
