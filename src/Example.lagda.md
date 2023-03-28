# Examples

\iffalse

```
{-# OPTIONS --overlapping-instances #-}
module Example where

open import Utils
open import Type
open import Core
open import Progress
open import Sugar
```

\fi

```
⦅⦆ : ∀ {Γ E} → Γ ⊢ ⟨ E ⟩ $𝕌
⦅⦆ = $ tt
```

## State

From "Handlers in Action".

The type of state is (currently) hard-coded as the type of natural numbers.
```
St : Type
St = $ ′ℕ
```

The state effect consists of `"get"` and `"put"` operations.
```
state : List Op
state = ("get" ∷ "put" ∷ [])
```

The state handler interprets a stateful computation as a function `St ⇒ ⟨ ε ⟩ A`.
The return clause returns the result `x : A`, ignoring the state.
The operation clause for `"get"` passes the current state to the continuation,
whereas the operation clause for `"put"` discards the current state and continues with the
value that the operation was called with.
```
state-handler : ∀ {Γ A}
  → Γ ⊢ ⟨ ¡ state ⟩ A ⇒ʰ ⟨ ε ⟩ (St ⇒ ⟨ ε ⟩ A)
state-handler = record
  { -- Hooks = "get" ∷ "put" ∷ []
  -- ;
    Hooks-handled = refl
  ; on-return = return! x ⇒ fun _ ⇒ x
  ; on-perform
      = handle! "get" ⇒ (λ _ k → fun s ⇒ k · s · s)
      ∣ handle! "put" ⇒ (λ s k → fun _ ⇒ k · ⦅⦆ · s)
      ∣ []
  }
```

```
state-handler☆ : ∀ {Γ A} → Γ ⊢ ⟨ ☆ ⟩ A ⇒ʰ ⟨ ☆ ⟩ (St ⇒ ⟨ ☆ ⟩ A)
state-handler☆ = record
  { Hooks-handled = refl
  ; on-return = return! x ⇒ fun _ ⇒ x
  ; on-perform
      = handle! "get" ⇒ (λ _ k → fun s ⇒ k · s · s)
      ∣ handle! "put" ⇒ (λ s k → fun _ ⇒ k · ⦅⦆ · s)
      ∣ []
  }
```

We wrap the handler in the following `run-state` function.
Note that this definition cannot be eta-reduced since
`handle state-handler (lift M)` is not a value.
```
--           M : {get,put,E} A
-- ------------------------------
-- run-state M : {F} (St ⇒ {E} A)
run-state : ∀ {Γ A}
  →  Γ ⊢ ⟨ ¡ state ⟩ A
  →  Γ ⊢ ⟨ ε ⟩       A
run-state M =
  handle state-handler M · $ 0
```

```
run-state☆ : ∀ {Γ A}
  →  Γ ⊢ ⟨ ☆ ⟩ A
  →  Γ ⊢ ⟨ ☆ ⟩ A
run-state☆ M =
  handle state-handler☆ M · $ 0
```

Some computation that uses state:
```
infixl 4 _|>_
pattern _|>_ N M = M · N

incr-state : ∀ {Γ} → Γ ⊢ ⟨ ¡ state ⟩ $ℕ
incr-state =
  Let x := perform! "get" ⦅⦆        In
  Let _ := perform! "put" (x + $ 1) In
  perform! "get" ⦅⦆

incr-state☆ : ∀ {Γ} → Γ ⊢ ⟨ ☆ ⟩ $ℕ
incr-state☆ =
  Let x := perform! "get" ⦅⦆        In
  Let _ := perform! "put" (x + $ 1) In
  perform! "get" ⦅⦆
```

Apply `run-state` to `incr-state`
```
state-example : ∀ {Γ} → Γ ⊢ ⟨ ε ⟩ $ℕ
state-example = run-state incr-state

state-example☆ : ∀ {Γ} → Γ ⊢ ⟨ ☆ ⟩ $ℕ
state-example☆ = run-state☆ incr-state☆

state-example☆ˡ : ∀ {Γ} → Γ ⊢ ⟨ ☆ ⟩ $ℕ
state-example☆ˡ = run-state☆ (castᵉ (+ (¡≤☆ {E = state})) incr-state)

state-example☆ʳ : ∀ {Γ} → Γ ⊢ ⟨ ε ⟩ $ℕ
state-example☆ʳ = run-state (castᵉ (- (¡≤☆ {E = state})) incr-state☆)
```

`state-example` reduces to the constant `$ 4`.
```
eval-state-example : ∃[ M—↠N ]
     eval (gas 25) state-example
  ≡  steps {⟨ ¡ [] ⟩ $ℕ} M—↠N (done ($ 1))
eval-state-example = _ , refl

eval-state-example☆ : ∃[ M—↠N ]
     eval (gas 25) state-example☆
  ≡  steps {⟨ ☆ ⟩ $ℕ} M—↠N (done ($ 1))
eval-state-example☆ = _ , refl

eval-state-example☆ˡ : ∃[ M—↠N ]
     eval (gas 25) state-example☆ˡ
  ≡  steps {⟨ ☆ ⟩ $ℕ} M—↠N (done ($ 1))
eval-state-example☆ˡ = _ , refl

eval-state-example☆ʳ : ∃[ M—↠N ]
     eval (gas 25) state-example☆ʳ
  ≡  steps {⟨ ¡ [] ⟩ $ℕ} M—↠N (done ($ 1))
eval-state-example☆ʳ = _ , refl
```

## Nondeterminism

Also from Handlers in Action.
A drunk tosses a coin: they may flip head or tails, or they may drop the coin
and it falls in the gutter.
```
nondet : Effect
nondet = ¡ ("choose" ∷ "fail" ∷ [])

fail : ∀ {Γ} → Γ ⊢ ⟨ nondet ⟩ $𝔹
fail =
  Let _ := perform! "fail" ⦅⦆ In
  ($ true) {- unreachable -}

drunkToss : ∅ ⊢ ⟨ nondet ⟩ $𝔹
drunkToss =
  Let catch-coin := perform! "choose" ⦅⦆ In
  if catch-coin
  ( Let coin-flip := perform! "choose" ⦅⦆ In
    if coin-flip ($ true) ($ false)
  )
  ( fail )
```

Handle a non-deterministic computation of type `𝔹`,
returning `true` when at least one execution returns `true`.
```
nondet-handler :
  ∅ ⊢ ⟨ nondet ⟩ $𝔹 ⇒ʰ ⟨ ε ⟩ $𝔹
nondet-handler = record
  { Hooks = "choose" ∷ "fail" ∷ []
  ; Hooks-handled = refl
  ; on-return = ` Z
  ; on-perform
      = handle! "choose" ⇒ (λ _ k → (k · tru) ⦅ _∨_ ⦆ (k · fls))
      ∣ handle! "fail" ⇒ (λ _ k → $ false)
      ∣ []
  }
```

```
nondet-example : ∅ ⊢ ⟨ ε ⟩ $𝔹
nondet-example =
  handle nondet-handler drunkToss
```

`nondet-example` reduces to the constant `$ true`.
\lyx{This takes a VERY (>20min) long time to evaluate. So we hide it from Agda for now}
```txt
from-steps : ∀ {P} {M : ∅ ⊢ P} → Steps M → Maybe (∅ ⊢ P)
from-steps (steps _ (done v)) = just (value v)
from-steps _ = nothing

eval-nondet-example : ∃[ M—↠N ]
     from-steps (eval (gas 1000) nondet-example)
  ≡  just ($ true)
eval-nondet-example = _ , refl
```
