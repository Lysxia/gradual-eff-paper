# Syntactic sugar

Some auxiliary definitions to write nice-looking examples.

```
module Sugar where

open import Utils
open import Type
open import Core
open import Progress
```

```
infix 1 _∋′_

_∋′_ : Context → Type → Set
Γ ∋′ A = ∀ {Δ E} → ⦃ ∀ {A} → ⦃ Γ ∋ A ⦄ → Δ ∋ A ⦄ → Δ ⊢ ⟨ E ⟩ A
```

```
infix 1 _↝ᴿ_

_↝ᴿ_ : Context → Context → Set
Γ ↝ᴿ Δ = ∀ {A} → ⦃ Γ ∋ A ⦄ → Δ ∋ A
```

```
ƛ-syntax : ∀ {Γ E F A B}
  → (⦃ Γ ↝ᴿ Γ ▷ A ⦄ → Γ ▷ A ∋′ A → Γ ▷ A ⊢ ⟨ E ⟩ B)
  → Γ ⊢ ⟨ F ⟩ (A ⇒ ⟨ E ⟩ B)
ƛ-syntax f = ƛ (f ⦃ S it ⦄ (λ ⦃ ρ ⦄ → ` ρ ⦃ Z ⦄))
```

```
infixr 1 ƛ-syntax
syntax ƛ-syntax (λ x → M) = fun x ⇒ M 
```

```
let-syntax : ∀ {Γ E A B}
  → (⦃ Γ ↝ᴿ Γ ▷ A ⦄ → Γ ▷ A ∋′ A → Γ ▷ A ⊢ ⟨ E ⟩ B)
  → Γ ⊢ ⟨ E ⟩ A
  → Γ ⊢ ⟨ E ⟩ B
let-syntax f M = (ƛ-syntax f) · M
```

```
infixr 1 let-syntax
syntax let-syntax (λ x → N) M = Let x := M In N
```

```
handle-syntax : ∀ {Γ E F A}
  → (e : Op)
  → (⦃ Γ ↝ᴿ Γ ▷ request e ▷ (response e ⇒ ⟨ E ⟩ A) ⦄
      → Γ ▷ request e ▷ (response e ⇒ ⟨ E ⟩ A) ∋′ request e
      → Γ ▷ request e ▷ (response e ⇒ ⟨ E ⟩ A) ∋′ (response e ⇒ ⟨ E ⟩ A)
      → Γ ▷ request e ▷ (response e ⇒ ⟨ E ⟩ A) ⊢ ⟨ E ⟩ A)
  → On-Perform Γ (⟨ E ⟩ A) F
  → On-Perform Γ (⟨ E ⟩ A) (e ∷ F)
handle-syntax e M Ms = M ⦃ S S it ⦄ (λ ⦃ ρ ⦄ → ` ρ ⦃ S Z ⦄) (λ ⦃ ρ ⦄ → ` ρ ⦃ Z ⦄) ∷ Ms
```

```
infixr 1 handle-syntax
syntax handle-syntax e M Ms = handle! e ⇒ M ∣ Ms
```

```
return-syntax : ∀ {Γ A P}
  → (⦃ Γ ↝ᴿ Γ ▷ A ⦄
      → Γ ▷ A ∋′ A
      → Γ ▷ A ⊢ P)
  → Γ ▷ A ⊢ P
return-syntax f = f ⦃ S it ⦄ (λ ⦃ ρ ⦄ → ` ρ ⦃ Z ⦄)

infixr 1 return-syntax
syntax return-syntax (λ x → M) = return! x ⇒ M
```

Automating membership proofs
```
record _by-cases_ (P : Set) (b : 𝔹) : Set where
  field
    unwrap : P

instance
  auto-∈☆ : ∀ {e} → e ∈☆ ☆
  auto-∈☆ = ☆

  auto-∈¡ : ∀ {e E} → ⦃ e ∈ E ⦄ → e ∈☆ ¡ E
  auto-∈¡ = ¡ it

  auto-∈ : ∀ {e e′} {E : List Op} → ⦃ (e ∈ e′ ∷ E) by-cases (does (e ≟ e′)) ⦄ → e ∈ e′ ∷ E
  auto-∈ ⦃ record { unwrap = e∈e′∷E } ⦄ = e∈e′∷E

  auto-∈-by-cases-true : ∀ {e} {E : List Op} → (e ∈ e ∷ E) by-cases true
  auto-∈-by-cases-true = record { unwrap = here refl }

  auto-∈-by-cases-false : ∀ {e e′} {E : List Op} → ⦃ e ∈ E ⦄ → (e ∈ e′ ∷ E) by-cases false
  auto-∈-by-cases-false = record { unwrap = there it }
```

Church encoding of booleans. I haven't implemented `if` for `′𝔹` yet.
```
-- 𝟚 = ★ ⇒ ⟨ ☆ ⟩ ★ ⇒ ⟨ ☆ ⟩ ⇒ ★

tru fls : ∀ {Γ E} → Γ ⊢ ⟨ E ⟩ 𝟚
tru = ƛ ƛ ` S Z
fls = ƛ ƛ ` Z

if : ∀ {Γ E A} → Γ ⊢ ⟨ E ⟩ 𝟚 → Γ ⊢ ⟨ E ⟩ A → Γ ⊢ ⟨ E ⟩ A → Γ ⊢ ⟨ E ⟩ A
if b t f = (cast (- ≤𝟚) b · (ƛ (lift {A = $ ′𝕌} t)) · (ƛ (lift {A = $ ′𝕌} f))) · $ tt
  where ≤𝟚 = A≤★ ⇒ ⟨ ≤☆ ⟩ A≤★ ⇒ ⟨ ≤☆ ⟩ A≤★
```

```
perform! : ∀ {Γ E} e → ⦃ e ∈☆ E ⦄ →
  Γ ⊢ ⟨ E ⟩ request e → Γ ⊢ ⟨ E ⟩ response e
perform! e M = perform- {e = e} it M refl
```
