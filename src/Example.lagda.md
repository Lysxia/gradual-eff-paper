# Examples

```
{-# OPTIONS --overlapping-instances #-}
module Example where

open import Utils
open import Type
open import Core
open import Progress
open import Sugar
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
state : Effect
state = ¡ ("get" ∷ "put" ∷ [])

state-handler : ∀ {Γ A}
  → Γ ⊢ ⟨ state ⟩ A ⇒ʰ ⟨ ε ⟩ (St ⇒ ⟨ ε ⟩ A)
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
state-handler :
  {get,put} A ⇒ʰ {} (St → {E} A)
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
run-state : ∀ {Γ A}
  →  Γ ⊢ ⟨ state ⟩ A
  →  Γ ⊢ ⟨ ε ⟩ (St ⇒ ⟨ ε ⟩ A)
run-state M =
  ƛ (handle state-handler (lift M) · ` Z)
```

Some computation that uses state:
```
infixl 4 _|>_
pattern _|>_ N M = M · N

⦅⦆ : ∀ {Γ E} → Γ ⊢ ⟨ E ⟩ $𝕌
⦅⦆ = $ tt

-- Given initial state x, this computes 2*(x+1).
some-comp : ∀ {Γ} → Γ ⊢ ⟨ state ⟩ $ℕ
some-comp =
  Let x := perform! "get" ⦅⦆        In
  Let _ := perform! "put" (x + $ 1) In
  Let y := perform! "get" ⦅⦆        In
  Let _ := perform! "put" (y + y)   In
  perform! "get" ($ tt)
```

Pseudocode:

```txt
!get ()      |> λ x →
!put (x + 1) |> λ _ →
!get ()      |> λ y →
!put (y + y) |> λ _ →
!get ()
```

Apply `run-state` to `some-comp`
```
state-example : ∀ {Γ} → Γ ⊢ ⟨ ε ⟩ $ℕ
state-example = run-state some-comp · $ 1
```

`state-example` reduces to the constant `$ 4`.
```
eval-state-example : ∃[ M—↠N ]
     eval (gas 25) state-example
  ≡  steps {⟨ ¡ [] ⟩ $ℕ} M—↠N (done ($ 4))
eval-state-example = _ , refl
```

## Nondeterminism

Also from Handlers in Action.
A drunk tosses a coin: they may flip head or tails, or they may drop the coin
and it falls in the gutter.
```
nondet : Effect
nondet = ¡ ("choose" ∷ "fail" ∷ [])

drunkToss : ∅ ⊢ ⟨ nondet ⟩ $𝔹
drunkToss =
  perform! "choose" ($ tt) |> ƛ (
  if (` Z)
     ( perform! "choose" ($ tt) |> ƛ (
       if (` Z) ($ true) ($ false))
     )
     ( perform! "fail" ($ tt) |> ƛ
       ($ true) {- unreachable -}))
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
      = ((` Z · tru) ⦅ _∨_ ⦆ (` Z · fls))
      ∷ $ false
      ∷ [] }
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
