# Examples

```
module Example where

open import Utils
open import Type
open import Core
open import Progress
```

## State

From "Handlers in Action".

The signatures of `"get"` and `"set"` are \lyx{currently} hard-coded,
with a state type `St` specialized to `ℕ`.
```
St : Type
St = $ ′ℕ
```

Definition of the state handler
```
state-handler : ∀ {Γ E A} → Γ ⊢ ⟨ ¡ ("get" ∷ "put" ∷ E) ⟩ A ➡ ⟨ ¡ E ⟩ (St ⇒ ⟨ ¡ E ⟩ A)
state-handler = record
  { Hooks = "get" ∷ "put" ∷ []
  ; Hooks-handled = refl
  ; on-return = ƛ (` S Z)
  ; on-perform
      = (ƛ ((` S Z) · (` Z) · (` Z)))
      ∷ (ƛ ((` S Z) · ($ tt) · (` S (S Z))) )
      ∷ []
  }
```

Same definition using human-readable syntax with named variables:
```txt
state-handler : {get,put,E} A  ➡  {E} (St → {E} A)
state-handler = handler
  | return x → λ _ → x
  | !get () k → λ s → k s s
  | !put s k → λ _ → k () s
```

Wrapping the handler as a `run-state` function.
Note: `handle state-handler (lift M)` is not a value so this cannot be
eta-reduced.
```
--           M : {get,put,E} A
-- ------------------------------
-- run-state M : {F} (St ⇒ {E} A)
run-state : ∀ {Γ E F A}
  →  Γ ⊢ ⟨ ¡ ("get" ∷ "put" ∷ E) ⟩ A
  →  Γ ⊢ ⟨ F ⟩ (St ⇒ ⟨ ¡ E ⟩ A)
run-state M =
  ƛ (handle state-handler (lift M) · ` Z)
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

Some computation that uses state:
```
infixl 4 _|>_
pattern _|>_ N M = M · N

perform! : ∀ {Γ E} e → ⦃ e ∈☆ E ⦄ → Γ ⊢ ⟨ E ⟩ request e → Γ ⊢ ⟨ E ⟩ response e
perform! e M = perform- {e = e} it refl M

-- Given initial state x, this computes 2*(x+1).
some-comp : ∀ {Γ E} → Γ ⊢ ⟨ ¡ ("get" ∷ "put" ∷ E) ⟩ $ℕ
some-comp =
  perform! "get" ($ tt)             |> ƛ (  -- !get ()      |> λ x →
  perform! "put" (` Z ⦅ _+_ ⦆ $ 1)  |> ƛ (  -- !put (x + 1) |> λ _ →
  perform! "get" ($ tt)             |> ƛ (  -- !get ()      |> λ y →
  perform! "put" (` Z ⦅ _+_ ⦆ ` Z)  |> ƛ (  -- !put (y + y) |> λ _ →
  perform! "get" ($ tt)))))                 -- !get ()
```

Apply `run-state` to `some-comp`
```
state-example : ∀ {Γ E} → Γ ⊢ ⟨ ¡ E ⟩ $ℕ
state-example = run-state some-comp · $ 1
```

`state-example` reduces to the constant `$ 4`.
```
eval-state-example : ∃[ M—↠N ]
     eval (gas 25) state-example
  ≡  steps {⟨ ¡ [] ⟩ $ℕ} M—↠N (done ($ 4))
eval-state-example = _ , refl
```
