# Motivation

\def\dhandler{\texttt{handler}_\texttt{dynamic}}
\def\shandler{\texttt{handler}_\texttt{static}}
\def\dclient{\texttt{client}_\texttt{dynamic}}
\def\sclient{\texttt{client}_\texttt{static}}

A key motivation for gradual types is to enable gradual migration
from dynamically typed code to statically typed code.
For instance, imagine that a library provides a dynamically typed
handler $\dhandler$, and one implements a $\dclient$ for that handler.
The end goal is to annotate those modules into a
$\shandler$ and a $\sclient$,
making explicit their input and output types, as well as the
effects that they perform. Here, the handler expects a computation
which uses the \texttt{state} effect, and produces a pure computation---with
the empty \texttt{ε} effect.

$$
\begin{array}{rl|rl}
  \dhandler & \texttt{(: ★ ⇒ ⟨ ☆ ⟩ ★) ⇒ ⟨ ☆ ⟩ ★} & \dclient & \texttt{: ★ ⇒ ⟨ ☆ ⟩ ★} \\
  \shandler & \texttt{: (ℕ ⇒ ⟨ state ⟩ ℕ) ⇒ ⟨ ε ⟩ ℕ} & \sclient & \texttt{: ℕ ⇒ ⟨ state ⟩ ℕ}
\end{array}
$$

For large code bases, it is desirable to do this progressively,
for example by migrating the handler first, or the client first,
or even alternatingly migrating parts of each artifact.
For this gradual migration to be effective, the composed program should still
be typeable and executable during those intermediate phases of the migration.

$$
\input{figures/migration.tex}
$$

When the statically typed handler is applied to the dynamically typed client,
the composed program is considered well-typed,
and casts are inserted to ensure that the client indeed behaves as expected by
the static argument type of the handler.

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
state : Effect
state = ¡ ("get" ∷ "put" ∷ [])
```

The state handler interprets a stateful computation as a function `St ⇒ ⟨ ε ⟩ A`.
The return clause returns the result `x : A`, ignoring the state.
The operation clause for `"get"` passes the current state to the continuation,
whereas the operation clause for `"put"` discards the current state and continues with the
value that the operation was called with.
```
state-handler : ∀ {Γ A}
  → Γ ⊢ ⟨ state ⟩ A ⇒ʰ ⟨ ε ⟩ (St ⇒ ⟨ ε ⟩ A)
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

We wrap the handler in the following `run-state` function.
Note that this definition cannot be eta-reduced since
`handle state-handler (lift M)` is not a value.
```
--           M : {get,put,E} A
-- ------------------------------
-- run-state M : {F} (St ⇒ {E} A)
run-state : ∀ {Γ A}
  →  Γ ⊢ ⟨ state ⟩ A
  →  Γ ⊢ ⟨ ε ⟩ (St ⇒ ⟨ ε ⟩ A)
run-state M =
  fun s ⇒ (handle state-handler (lift M) · s)
```

Some computation that uses state:
```
infixl 4 _|>_
pattern _|>_ N M = M · N

-- Given initial state x, this computes 2*(x+1).
some-comp : ∀ {Γ} → Γ ⊢ ⟨ state ⟩ $ℕ
some-comp =
  Let x := perform! "get" ⦅⦆        In
  Let _ := perform! "put" (x + $ 1) In
  Let y := perform! "get" ⦅⦆        In
  Let _ := perform! "put" (y + y)   In
  perform! "get" ⦅⦆
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

TODO: Dynamic version:

```
postulate run-state-dyn : ∅ ⊢ ⟨ ☆ ⟩ ★ → ∅ ⊢ ⟨ ☆ ⟩ (★ ⇒ ⟨ ☆ ⟩ ★)
postulate some-comp-dyn : ∅ ⊢ ⟨ ☆ ⟩ ★

state-example-dyn : ∅ ⊢ ⟨ ☆ ⟩ ★
state-example-dyn = run-state-dyn some-comp-dyn · (($ 1) ⇑ $ ′ℕ)
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
