```
module Auto where

open import Utils
open import Type
open import Core
open import Progress
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
if b t f = (cast (- ⟨ id ⟩ ≤𝟚) b · (ƛ (lift {A = $ ′𝕌} t)) · (ƛ (lift {A = $ ′𝕌} f))) · $ tt
  where ≤𝟚 = A≤★ ⇒ ⟨ ≤☆ ⟩ A≤★ ⇒ ⟨ ≤☆ ⟩ A≤★
```

```
perform! : ∀ {Γ E} e → ⦃ e ∈☆ E ⦄ →
  Γ ⊢ ⟨ E ⟩ request e → Γ ⊢ ⟨ E ⟩ response e
perform! e M = perform- {e = e} it M refl
```
