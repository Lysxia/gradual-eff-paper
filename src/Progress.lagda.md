# Operational Semantics

In this section, we define the operational semantics as a small-step
reduction relation. We prove progress, and since the proof is constructive,
it doubles as an evaluation function which we can apply on examples.

\iffalse
```
module Progress where

open import Utils
open import Type
open import Core

import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any.Properties as Any
```
\fi

\iffalse
```
private variable
  A A′ B C G : Type
  E E′ F : Effect
  P P′ Q Q′ R : CType
  Γ Δ : Context
```
\fi

## Frames

```
infix  5 [_]⇑_
infix  5 `cast_[_]
infix  6 [_]·_
infix  6 _·[_]
infix  6 [_]⦅_⦆_
infix  6 _⦅_⦆[_]
infix  7 _⟦_⟧
```

Frames are "terms with a hole".
Frames are also known as evaluation contexts, but the identifier `Context` is
already taken in our development.
They are used to define a congruence rule for reduction, \ie{} the contexts
under which reduction may happen, as well as to represent continuations for
effect handlers.

`\begin{AgdaAlign}`{=tex}
```
data Frame (Γ : Context) (C : CType) :
  CType → Set where
```

The base case is the empty frame.
```
  □ : Frame Γ C C
```

There are two frame constructors for applications: one
where the hole is on the left of the application `_·_`,
and one where the hole is on the right.
To make the semantics deterministic, we require that we can
only focus on the right operand once the left one is a value.
```
  [_]·_ :
       (ℰ : Frame Γ C (⟨ E ⟩ (A ⇒ ⟨ E ⟩ B)))
    →  (M : Γ ⊢ ⟨ E ⟩ A)
       ---------------
    →  Frame Γ C (⟨ E ⟩ B)

  _·[_] : {V : Γ ⊢ ⟨ E ⟩ (A ⇒ ⟨ E ⟩ B)}
    →  (v : Value V)
    →  (ℰ : Frame Γ C (⟨ E ⟩ A))
       ----------------
    →  Frame Γ C (⟨ E ⟩ B)
```

Primitive operators follow the same logic, requiring the left operand
to be a value before reducing the right operand.
```
  [_]⦅_⦆_ : ∀ {ι ι′ ι″}
    →  (ℰ : Frame Γ C (⟨ E ⟩ ($ ι)))
    →  (_⊕_ : rep ι → rep ι′ → rep ι″)
    →  (N : Γ ⊢ ⟨ E ⟩ ($ ι′))
       ------------------
    →  Frame Γ C (⟨ E ⟩ ($ ι″))

  _⦅_⦆[_] : ∀ {ι ι′ ι″} {V : Γ ⊢ ⟨ E ⟩ $ ι}
    →  (v : Value V)
    →  (_⊕_ : rep ι → rep ι′ → rep ι″)
    →  (ℰ : Frame Γ C (⟨ E ⟩ ($ ι′)))
       -------------------
    →  Frame Γ C (⟨ E ⟩ ($ ι″))
```

The other constructors represent term constructors
with only one immediate subterm.
```
  [_]⇑_ : ∀ {E G}
    →  (ℰ : Frame Γ C (⟨ E ⟩ G))
    →  (g : Ground G)
       --------------
    →  Frame Γ C (⟨ E ⟩ ★)

  `cast_[_] : ∀ {P Q}
    →  (±p : P =>ᶜ Q)
    →  (ℰ : Frame Γ C P)
       -------------
    →  Frame Γ C Q

  ″perform_[_]_ : ∀ {E e}
    →  e ∈☆ E
    →  Frame Γ C (⟨ E ⟩ request e)
    →  ∀ {A}
    →  response e ≡ A
    →  Frame Γ C (⟨ E ⟩ A)

  ′handle_[_] : ∀ {P Q}
    →  Γ ⊢ P ⇒ʰ Q
    →  Frame Γ C P
       -----------
    →  Frame Γ C Q

pattern ′perform_[_] e ℰ
  = ″perform e [ ℰ ] refl
```
`\end{AgdaAlign}`{=tex}

The plug function inserts an expression into the hole of a frame.
```
_⟦_⟧ : ∀{Γ P B} → Frame Γ P B → Γ ⊢ P → Γ ⊢ B
□ ⟦ M ⟧                 =  M
([ ℰ ]· M) ⟦ L ⟧        =  ℰ ⟦ L ⟧ · M
(v ·[ ℰ ]) ⟦ M ⟧        =  value v · ℰ ⟦ M ⟧
([ ℰ ]⦅ _⊕_ ⦆ N) ⟦ M ⟧  =  ℰ ⟦ M ⟧ ⦅ _⊕_ ⦆ N
(v ⦅ _⊕_ ⦆[ ℰ ]) ⟦ N ⟧  =  value v ⦅ _⊕_ ⦆ ℰ ⟦ N ⟧
([ ℰ ]⇑ g) ⟦ M ⟧        =  ℰ ⟦ M ⟧ ⇑ g
(`cast ±p [ ℰ ]) ⟦ M ⟧  =  cast ±p (ℰ ⟦ M ⟧)
(′handle H [ ℰ ]) ⟦ M ⟧ = handle H (ℰ ⟦ M ⟧)
(″perform e [ ℰ ] eq) ⟦ M ⟧
  = perform- e (ℰ ⟦ M ⟧) eq
```

Composition of two frames
```
_∘∘_ : Frame Γ Q R → Frame Γ P Q → Frame Γ P R
□ ∘∘ 𝐹                 =  𝐹
([ ℰ ]· M) ∘∘ 𝐹        =  [ ℰ ∘∘ 𝐹 ]· M
(v ·[ ℰ ]) ∘∘ 𝐹        =  v ·[ ℰ ∘∘ 𝐹 ]
([ ℰ ]⦅ _⊕_ ⦆ N) ∘∘ 𝐹  =  [ ℰ ∘∘ 𝐹 ]⦅ _⊕_ ⦆ N
(v ⦅ _⊕_ ⦆[ ℰ ]) ∘∘ 𝐹  =  v ⦅ _⊕_ ⦆[ ℰ ∘∘ 𝐹 ]
([ ℰ ]⇑ g) ∘∘ 𝐹        =  [ ℰ ∘∘ 𝐹 ]⇑ g
(`cast ±p [ ℰ ]) ∘∘ 𝐹  =  `cast ±p [ ℰ ∘∘ 𝐹 ]
(′handle H [ ℰ ]) ∘∘ 𝐹 =  ′handle H [ ℰ ∘∘ 𝐹 ]
(″perform e [ ℰ ] eq) ∘∘ 𝐹
  = ″perform e [ ℰ ∘∘ 𝐹 ] eq
```

Composition and plugging
```
∘∘-lemma : ∀ {Γ P B C}
  → (ℰ : Frame Γ B C)
  → (𝐹 : Frame Γ P B)
  → (M : Γ ⊢ P)
    -----------------------------
  → ℰ ⟦ 𝐹 ⟦ M ⟧ ⟧ ≡ (ℰ ∘∘ 𝐹) ⟦ M ⟧
```

\iffalse
```
∘∘-lemma □ 𝐹 M                                         =  refl
∘∘-lemma ([ ℰ ]· M₁) 𝐹 M       rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
∘∘-lemma (v ·[ ℰ ]) 𝐹 M        rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
∘∘-lemma ([ ℰ ]⦅ _⊕_ ⦆ N) 𝐹 M  rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
∘∘-lemma (v ⦅ _⊕_ ⦆[ ℰ ]) 𝐹 M  rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
∘∘-lemma ([ ℰ ]⇑ g) 𝐹 M        rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
∘∘-lemma (`cast ±p [ ℰ ]) 𝐹 M  rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
∘∘-lemma (″perform e [ ℰ ] eq) 𝐹 M rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
∘∘-lemma (′handle H [ ℰ ]) 𝐹 M rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
```
\fi

Renaming on frames.
```
renᶠ : Γ →ᴿ Δ → Frame Γ P Q → Frame Δ P Q
```

\iffalse
```
renᶠ ρ □ = □
renᶠ ρ ([ ℰ ]· M) = [ renᶠ ρ ℰ ]· ren ρ M
renᶠ ρ (v ·[ ℰ ]) = ren-val ρ v ·[ renᶠ ρ ℰ ]
renᶠ ρ ([ ℰ ]⦅ f ⦆ M) = [ renᶠ ρ ℰ ]⦅ f ⦆ ren ρ M
renᶠ ρ (v ⦅ f ⦆[ ℰ ]) = ren-val ρ v ⦅ f ⦆[ renᶠ ρ ℰ ]
renᶠ ρ ([ ℰ ]⇑ g) = [ renᶠ ρ ℰ ]⇑ g
renᶠ ρ (`cast ±p [ ℰ ]) = `cast ±p [ renᶠ ρ ℰ ]
renᶠ ρ (″perform e [ ℰ ] eq) = ″perform e [ renᶠ ρ ℰ ] eq
renᶠ ρ (′handle H [ ℰ ]) = ′handle (renʰ ρ H) [ renᶠ ρ ℰ ]
```
\fi

```
liftᶠ : Frame Γ P Q → Frame (Γ ▷ A) P Q
liftᶠ = renᶠ S_

liftʰ : Γ ⊢ P ⇒ʰ Q → Γ ▷ A ⊢ P ⇒ʰ Q
liftʰ = renʰ S_
```

The effect in the codomain of the cast. 
```
cast-effect : P =>ᶜ Q → Effect
cast-effect {Q = ⟨ E ⟩ B} _ = E
```

`handled e ℰ` means that the operation `e` is handled by the evaluation context `ℰ`:
either `ℰ` contains a handler where `e` is one of its hooks, or `ℰ` contains a cast
where `e` is not allowed by the codomain of the cast.
```
handled : ∀ e → Frame Γ P Q → Set
handled e □ = ⊥
handled e (′handle H [ ℰ ])
  = e ∈ H .Hooks ⊎ handled e ℰ
handled {Q = ⟨ E ⟩ _} e (`cast ±p [ ℰ ])
  = (¬ e ∈☆ E) ⊎ handled e ℰ  -- ±p : P => ⟨ E ⟩ B
handled e ([ ℰ ]· M) = handled e ℰ
handled e (M ·[ ℰ ]) = handled e ℰ
handled e ([ ℰ ]⦅ f ⦆ M) = handled e ℰ
handled e (M ⦅ f ⦆[ ℰ ]) = handled e ℰ
handled e ([ ℰ ]⇑ g) = handled e ℰ
handled e (″perform e′∈E [ ℰ ] eq) = handled e ℰ
```

Note: for casts, this definition always checks whether `e` is in the codomain.

An evaluation context `ℰ₀` containing only an upcast may never raise blame: no
effects are handled by `ℰ₀`.

```
upcast-safety : ∀ {Γ P Q} (P≤Q : P ≤ᶜ Q) →
  let  ℰ₀ : Frame Γ P Q
       ℰ₀ = `cast (+ P≤Q) [ □ ] in
  ∀ (e : Op) → e ∈☆ CType.effects P → ¬ handled e ℰ₀
upcast-safety (⟨ ¡≤☆ ⟩ _) e e∈E (inj₁ ¬e∈☆)
  = ¬e∈☆ ☆
upcast-safety (⟨ id  ⟩ _) e e∈E (inj₁ ¬e∈E)
  = ¬e∈E e∈E
```

An operation `e` is not handled by a cast `±p` if `e` is not an element of the
target effect of the cast.
```
¬handled-cast : ∀ {e}
    {±p : (⟨ E ⟩ A) =>ᶜ (⟨ F ⟩ B)}
    (ℰ : Frame Γ P (⟨ E ⟩ A))
  → e ∈☆ F
  → ¬ handled e ℰ
    -------------------------
  → ¬ handled e (`cast ±p [ ℰ ])
¬handled-cast ℰ e∈F ¬e//ℰ (inj₁ ¬e∈F)
  = ¬e∈F e∈F
¬handled-cast ℰ e∈F ¬e//ℰ (inj₂ e//ℰ)
  = ¬e//ℰ e//ℰ
```

An operation `e` is not handled by a handler if `e` is not one of its hooks.
```
¬handled-handle : ∀ {e}
    {H : Γ ⊢ P ⇒ʰ Q} (ℰ : Frame Γ P′ P)
  → ¬ e ∈ Hooks H
  → ¬ handled e ℰ
    -----------------------------
  → ¬ handled e (′handle H [ ℰ ])
¬handled-handle ℰ ¬e∈H ¬e//ℰ (inj₁ e∈H)
  = ¬e∈H e∈H
¬handled-handle ℰ ¬e∈H ¬e//ℰ (inj₂ e//ℰ)
  = ¬e//ℰ e//ℰ
```

Consistent membership is preserved by concatenation.
```
∈☆-++☆ʳ : ∀ {e Eh} → e ∈☆ E → e ∈☆ (Eh ++☆ E)
∈☆-++☆ʳ {Eh = Eh} (¡ e) = ¡ (Any.++⁺ʳ Eh e)
∈☆-++☆ʳ ☆ = ☆
```

Inversion lemma for consistent membership.
```
∈☆-++☆⁻ : ∀ {e Eh} → e ∈☆ (Eh ++☆ E)
  → e ∈ Eh ⊎ e ∈☆ E
∈☆-++☆⁻ {E = ☆} _ = inj₂ ☆
∈☆-++☆⁻ {E = ¡ _} {Eh = Eh} (¡ e∈++)
    with Any.++⁻ Eh e∈++
... | inj₁ e∈Eh = inj₁ e∈Eh
... | inj₂ e∈E = inj₂ (¡ e∈E)
```

If a computation under a handler raises an effect `e` which is
not a hook of the handler, then `e` must be in the resulting effect
of the handler.
```
¬∈-handler : ∀ {e} (H : Γ ⊢ ⟨ E ⟩ A ⇒ʰ ⟨ F ⟩ B) → e ∈☆ E → ¬ e ∈ H .Hooks → e ∈☆ F
¬∈-handler H e∈E ¬e∈H rewrite Hooks-handled H
    with ∈☆-++☆⁻ e∈E
... | inj₁ e∈H = ⊥-elim (¬e∈H e∈H)
... | inj₂ e∈F = e∈F
```

Double negation elimination for decidable predicates.
```
¬¬-dec : ∀ {P : Set} → Dec P → ¬ ¬ P → P
¬¬-dec (yes p) _ = p
¬¬-dec (no ¬p) ¬¬p = ⊥-elim (¬¬p ¬p)
```

```
¬handled-∈ : ∀ {e}
    (ℰ : Frame Γ (⟨ E ⟩ A) (⟨ F ⟩ B))
  → ¬ handled e ℰ → e ∈☆ E → e ∈☆ F
¬handled-∈ □ _ e = e
¬handled-∈ ([ ℰ ]· M) = ¬handled-∈ ℰ
¬handled-∈ (v ·[ ℰ ]) = ¬handled-∈ ℰ
¬handled-∈ ([ ℰ ]⦅ _⊕_ ⦆ N) = ¬handled-∈ ℰ
¬handled-∈ (v ⦅ _⊕_ ⦆[ ℰ ]) = ¬handled-∈ ℰ
¬handled-∈ ([ ℰ ]⇑ g) = ¬handled-∈ ℰ
¬handled-∈ (″perform e [ ℰ ] x₁) = ¬handled-∈ ℰ
¬handled-∈ (`cast ±p [ ℰ ]) ¬e//ℰ e
  = ¬¬-dec (_ ∈☆? _) (¬e//ℰ ∘ inj₁)
¬handled-∈ (′handle H [ ℰ ]) ¬e//ℰ e
  = ¬∈-handler H (¬handled-∈ ℰ (¬e//ℰ ∘ inj₂) e) (¬e//ℰ ∘ inj₁)
```

## Decomposing a cast

The following construction unifies the behaviors of some casts.
```
infix 6 _==>_

data _==>_ : Type → Type → Set where

  id : ∀ {A}
      -------
    → A ==> A

  _⇒_ : ∀ {A A′ P P′}
    → A′ => A
    → P =>ᶜ P′
      -----------------
    → A ⇒ P ==> A′ ⇒ P′

  other : ∀ {A B}
      -------
    → A ==> B

split : ∀ {A B} → A => B → A ==> B
split (+ id)     =  id
split (- id)     =  id
split (+ s ⇒ t)  =  (- s) ⇒ (+ t)
split (- s ⇒ t)  =  (+ s) ⇒ (- t)
split (+ p ⇑ g)  =  other
split (- p ⇑ g)  =  other
split (* id)     =  id
split (* s ⇒ t)  =  (* s) ⇒ (* t)
```

Safe casts are only `id` or `_⇒_`.
```
split-*≢other :
  (q : A ⊑ B) → split (* q) ≢ other
split-*≢other id ()
```

```
splitᶜ : ∀ {E F A B}
  →  (⟨ E ⟩ A) =>ᶜ (⟨ F ⟩ B)
     -----------------------
  →  A ==> B
splitᶜ = split ∘ =>ᶜ-returns
```

## Wrapping functions

```
infix 2 _↦_ _—→_

ƛ-wrap : ∀ (∓s : A′ => A) (±t : P =>ᶜ P′) 
  → (∀ {E} → Γ ⊢ ⟨ E ⟩ (A ⇒ P))
  → (∀ {E} → Γ ⊢ ⟨ E ⟩ (A′ ⇒ P′))
ƛ-wrap ∓s ±t M =
  ƛ cast ±t (lift M · (cast (pure± ∓s) (` Z)))
```

## Reduction

We first define a reduction relation `_↦_` on redexes,
and then close it under congruence, as `_—↠_`.

```
data _↦_ {Γ} :
  ∀ {P} → (_ _ : Γ ⊢ P) → Set where
```

Because there are effects in our type system,
we must modify the β rule a bit from its standard
formulation. In the application `(ƛ N) · W`, the value
`W` is a term with some effect `E`, but when substituting
`W` in `N`, the substituted variable may occur in contexts
with different effects `E`, in which case `W` would be
an ill-typed replacement. Hence we generalize `W` before applying a
substitution.
\lyx{This explanation should be moved either to the definition of `gvalue` or of substitution.}

```
  β : ∀ {N : Γ ▷ A ⊢ ⟨ E ⟩ B} {W : Γ ⊢ ⟨ E ⟩ A}
    → (w : Value W)
      --------------------
    → (ƛ N) · W ↦ N [ gvalue w ]
```

The `δ` rule reduces primitive operators applied to constants.
```
  δ : ∀ {ι ι′ ι″}
      {_⊕_ : rep ι → rep ι′ → rep ι″}
      {k : rep ι} {k′ : rep ι′}
      --------------------------------------------
    → _⦅_⦆_ {E = E} ($ k) _⊕_ ($ k′) ↦ $ (k ⊕ k′)
```

The next six rules have to do with casts. The first five are based on standard
cast calculus rules, describing how to cast values. The sixth is a rule related
to casting effects.

The `ident` rule removes identity casts, after the casted computation returned
a value.
```
  ident : ∀ {V : Γ ⊢ ⟨ E ⟩ A}
      {±p : (⟨ E ⟩ A) =>ᶜ ⟨ F ⟩ A}
    → splitᶜ ±p ≡ id
    → (v : Value V)
      --------------
    → cast ±p V ↦ gvalue v
```

The `wrap` rule reduces casts between function types.
The cast `±p` is split into two casts, `∓s` between domains and `±t` codomains;
the function being cast is wrapped using `ƛ-wrap`, composing it with those two casts.
```
  wrap : {N : Γ ▷ A ⊢ P}
      {∓s : A′ => A} {±t : P =>ᶜ P′}
      {±p : ⟨ E ⟩ (A ⇒ P) =>ᶜ ⟨ E′ ⟩ (A′ ⇒ P′)}
    → splitᶜ ±p ≡ ∓s ⇒ ±t
      -----------------------------------------
    → cast ±p (ƛ N) ↦ ƛ-wrap ∓s ±t (ƛ N)
```

The `expand` rule reduces an upcast to `★` to a box.
\lyx{and does something more with `p`}
```
  expand : ∀{V : Γ ⊢ ⟨ E ⟩ A}
      {p : A ≤ G} {E≤E′ : E ≤ᵉ E′}
    → Value V
    → (g : Ground G)
      -------------------------------
    → cast (+ ⟨ E≤E′ ⟩ (p ⇑ g)) V ↦ cast (+ ⟨ E≤E′ ⟩ p) V ⇑ g
```

The `collapse` rule reduces a downcast `(p ⇑ g)` from `★`, in which case
the value under the cast must be a box `(V ⇑ g)`, by unwrapping
the box, provided the tag `g` in the box and in the cast match.
\lyx{and does something more with `p`}
```
  collapse : ∀ {V : Γ ⊢ ⟨ E ⟩ G}
      {p : A ≤ G} {E′≤E : E′ ≤ᵉ E}
    → Value V
    → (g : Ground G)
      --------------------------------
    →   cast (- ⟨ E′≤E ⟩ (p ⇑ g)) (V ⇑ g)
      ↦ cast (- ⟨ E′≤E ⟩ p) V
```

The `collide` rule reduces a downcast `(p ⇑ h)` applied to
a box `(V ⇑ g)` when the tags `g` and `h` don't match.
This raises `blame`.
```
  collide : ∀{G H} {V : Γ ⊢ ⟨ E ⟩ G}
      {p : A ≤ H} {E′≤E : E′ ≤ᵉ E}
    → Value V
    → (g : Ground G)
    → (h : Ground H)
    → G ≢ H
      -----------------------------
    → cast (- ⟨ E′≤E ⟩ (p ⇑ h)) (V ⇑ g) ↦ blame
```

Casts contain both a cast on values (whose behavior is defined by the previous five rules),
and a cast on effects. The next rule describes how such a cast may fail: the computation
under the cast performs an effect which:
is not handled by any inner handler and is not a member of the target effect `F` of the cast.

```
  blameᵉ : ∀ {e} {e∈E′ : e ∈☆ E′} {V} {M}
      {ℰ : Frame Γ (⟨ E′ ⟩ response e) (⟨ E ⟩ A)}
      {±p : ⟨ E ⟩ A =>ᶜ ⟨ F ⟩ B}
    → ¬ e ∈☆ F
    → ¬ handled e ℰ
    → Value V
    → M ≡ ℰ ⟦ perform e∈E′ V ⟧
      ---------------------------
    → cast ±p M ↦ blame
```

Note that there is no rule for "successful effect casts". When an effect passes successfully
through a cast, it simply keeps being raised until a matching handler or cast is found.

Handlers have two rules. When the handled computation returns a value, the
return clause is invoked.
```
  handle-value : ∀ {H : Γ ⊢ P ⇒ʰ Q} {V}
    → (v : Value V)
      --------------
    → handle H V  ↦  on-return H [ gvalue v ]
```

When the handled computation performs an operation, the corresponding operation
clause of the closest matching handler is invoked.
This rule expressed in Agda looks rather complex.

In the right-hand side of the reduction, `All.lookup` finds the corresponding
clause, given a proof that the operation `e` is an element of the handler's
`Hooks`. Two substitutions follow, because operation clauses extend the
context with two variables, one for the operation's request payload, and
one for the continuation. Since the continuation variable occurs at the end of
the context, it must be substituted first.

```text
clause : Γ ▷ request e ▷ (response e ⇒ Q) ⊢ Q
```

```
  handle-perform : ∀ {e} {e∈E : e ∈☆ E}
      {H : Γ ⊢ P ⇒ʰ Q} {V ℰ e∈Hooks}
    → (v : Value V)
    → ¬ handled e ℰ
      -- ensures H is the first matching handler
    → (e ∈? Hooks H) ≡ yes e∈Hooks
      -- ensures this is the first matching clause within H
      -- TODO: a more declarative reformulation?
    → handle H (ℰ ⟦ perform e∈E V ⟧)
      ↦ All.lookup (on-perform H) e∈Hooks
          [ ƛ (handle (liftʰ (liftʰ H)) (liftᶠ (liftᶠ ℰ) ⟦ ` Z ⟧)) ]
          [ gvalue v ]
```

TODO: explain the order of these substitutions and why the 2 lifts.
TODO: we can avoid one lift by doing a simultaneous substitution, but there is still one left.

The top-level reduction relation `_—↠_` allows reduction to happen under any
frame. Again, we use fording to keep the frame substitution function out of the
type's indices.
```
data _—→_ :
  (Γ ⊢ P) → (Γ ⊢ P) → Set where

  ξξ :
       {M N : Γ ⊢ P} {M′ N′ : Γ ⊢ Q}
    →  (ℰ : Frame Γ P Q)
    →  M′ ≡ ℰ ⟦ M ⟧
    →  N′ ≡ ℰ ⟦ N ⟧
    →  M ↦ N
       --------
    →  M′ —→ N′
```

Notation to hide the fording indices.
```
pattern ξ ℰ M—→N = ξξ ℰ refl refl M—→N
```

That makes `ξ` a constructor with the following type:

    ξ  :  (ℰ : Frame Γ P Q)
       →  M ↦ N
          --------
       →  ℰ ⟦ M ⟧ —→ ℰ ⟦ N ⟧

## Reflexive and transitive closure of reduction

```
infixr 1 _++↠_
infix  1 begin_
infix  2 _—↠_
infixr 2 _—→⟨_⟩_ _—↠⟨_⟩_
infix  3 _∎

data _—↠_ : Γ ⊢ P → Γ ⊢ P → Set where

  _∎ : (M : Γ ⊢ P)
      ---------
    → M —↠ M

  _—→⟨_⟩_ : (L : Γ ⊢ P) {M N : Γ ⊢ P}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : {M N : Γ ⊢ P}
  → (M —↠ N) → (M —↠ N)
begin M—↠N = M—↠N
```

Convenience function to build a sequence of length one.
```
unit : {M N : Γ ⊢ P} → (M ↦ N) → (M —↠ N)
unit {M = M} {N = N} M↦N
  = M —→⟨ ξ □ M↦N ⟩ N ∎
```

Apply ξ to each element of a sequence
```
ξ* : {M N : Γ ⊢ P} → (E : Frame Γ P Q)
  → M —↠ N
    ------------------
  → E ⟦ M ⟧ —↠ E ⟦ N ⟧
ξ* E (M ∎) = E ⟦ M ⟧ ∎
ξ* E (L —→⟨ ξξ {M = L′} {N = M′}
               F refl refl L′↦M′ ⟩ M—↠N)
  =  E ⟦ L ⟧
     —→⟨ ξξ (E ∘∘ F) (∘∘-lemma E F L′)
         (∘∘-lemma E F M′) L′↦M′ ⟩
     ξ* E M—↠N
```

Concatenate two sequences.
```
_++↠_ : {L M N : Γ ⊢ P}
  → L —↠ M
  → M —↠ N
    ------
  → L —↠ N
(M ∎) ++↠ M—↠N =  M—↠N
(L —→⟨ L—→M ⟩ M—↠N) ++↠ N—↠P
  = L —→⟨ L—→M ⟩ (M—↠N ++↠ N—↠P)
```

Alternative notation for sequence concatenation.
```
_—↠⟨_⟩_ : (L : Γ ⊢ P) {M N : Γ ⊢ P}
  → L —↠ M
  → M —↠ N
    ------
  → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N  =  L—↠M ++↠ M—↠N
```

## Irreducible terms

Values are irreducible.
```
value-irreducible : {V M : Γ ⊢ P}
  →  Value V
     ----------
  →  ¬ (V —→ M)
value-irreducible () (ξ □ (β x))
value-irreducible ()
  (ξξ (″perform _ [ _ ] _) refl _ _)
value-irreducible (v ⇑ g) (ξ ([ E ]⇑ g) V—→M)
  =  value-irreducible v (ξ E V—→M)
```

Variables are irreducible.
```
variable-irreducible : ∀ {x : Γ ∋ A} {N : Γ ⊢ ⟨ E ⟩ A}
     ------------
  →  ¬ (` x —→ N)
variable-irreducible (ξξ □ refl _ ())
```

Boxes are irreducible (at the top level)
```
box-irreducible :
     {M : Γ ⊢ ⟨ E ⟩ G} {N : Γ ⊢ ⟨ E ⟩ ★}
  →  (g : Ground G)
     --------------
  →  ¬ (M ⇑ g ↦ N)
box-irreducible g ()
```

Blame is irreducible.
```
blame-irreducible : ∀ {M′ : Γ ⊢ P}
    ---------------
 →  ¬ (blame —→ M′)
blame-irreducible (ξ □ ())
```

## Progress

Every term that is well typed and closed either takes
a reduction step or belongs to one of several well-defined
classes of normal forms: `blame`, a value, or a `pending`
operation in some context.
The following data type lists those possible cases.
```
data Progress {P} : (∅ ⊢ P) → Set where

  step : ∀ {M N : ∅ ⊢ P}
    →  M —→ N
       ----------
    →  Progress M

  done : ∀ {M : ∅ ⊢ P}
    →  Value M
       ----------
    →  Progress M

  blame : ∀ {Q}
    →  (E : Frame ∅ Q P)
       ---------------------
    →  Progress (E ⟦ blame ⟧)

  pending : ∀ {e} {V} ℰ
    →  (e∈E : e ∈☆ E)
    →  Value V
    →  ¬ handled e ℰ
       ------------------
    →  Progress (ℰ ⟦ perform e∈E V ⟧)
```

As one subcase of the proof of progress, we prove that a `cast` applied to a
value always takes a step.
```
progress± : ∀ {V : ∅ ⊢ P}
  → (v : Value V)
  → (±p : P =>ᶜ Q)
    --------------------
  → ∃[ M ](cast ±p V ↦ M)
```

Note that the effect component of the cast is ignored because the term under
the cast is a value. Only the value cast matters.
The reduction rule to be applied depends on the structure of the `cast`.
We first try to `split` the cast.
```
progress± v ±p with splitᶜ ±p in e
```

If the cast is an identity cast, then the `ident` rule applies, removing the
cast.
```
progress± v     _ | id                       =  _ , ident e v
```

If the cast is between functions, then the `wrap` rule applies,
wrapping the input and output of the function in casts.
```
progress± (ƛ _) _ | _ ⇒ _                    =  _ , wrap e
```

Otherwise, we have a cast to or from the dynamic type `★`.
If it is an upcast to `★`, the `expand` rule wraps the value in a box.
```
progress± v       (+ ⟨ _ ⟩ (_ ⇑ g))
  | other  =  _ , expand v g
```

If it is a downcast from `★`, the cast value must be a box.
A run-time tag comparison is performed. If the tags match, we unbox the box
with `collapse`. If the tags don't match, we raise blame with `collide`.
```
progress± (v ⇑ g) (- ⟨ _ ⟩ (_ ⇑ h)) | other
    with ground g ≡? ground h
... | yes refl rewrite uniqueG g h
  =  _ , collapse v h
... | no  G≢H
  =  _ , collide v g h G≢H
```

Safe casts `(* q`) are either identity casts or function casts, so the `other` case is
vacuous for those.
```
progress± _ (* ⟨ _ ⟩ q) | other
  =  ⊥-elim (split-*≢other q e)
```

We finally reach the proof of progress.
```
progress :
    (M : ∅ ⊢ P)
    -----------
  → Progress M
```

Abstractions and constants are values.
```
progress (ƛ N)                           =  done (ƛ N)
progress ($ k)                           =  done ($ k)
```

Blame is in its own category in the progress theorem.
```
progress blame                           =  blame □
```

To reduce an application, we first try to reduce the function subterm.
The `blame`, `step`, and `pending` cases are propagated accordingly (by congruence).
If the function is already a value (`done (ƛ N)`), we try to reduce
its argument. If both operands of the application are values (`done w`),
we may take a `β` step.
```
progress (L · M) with progress L
... | blame ℰ =  blame ([ ℰ ]· M)
... | step (ξ ℰ L↦L′)
    =  step (ξ ([ ℰ ]· M) L↦L′)
... | pending ℰ e v ¬e//ℰ
    = pending ([ ℰ ]· M) e v ¬e//ℰ
... | done (ƛ N) with progress M
...     | done w      =  step (ξ □ (β w))
...     | blame ℰ =  blame ((ƛ N) ·[ ℰ ])
...     | step (ξ ℰ M↦M′)
        = step (ξ ((ƛ N) ·[ ℰ ]) M↦M′)
...     | pending ℰ e v ¬e//ℰ
        =  pending ((ƛ N) ·[ ℰ ]) e v ¬e//ℰ
```

Primitive operators behave similarly. We try to reduce each operand,
and if both are values, we may take a `δ` step.
```
progress (L ⦅ _⊕_ ⦆ M) with progress L
... | blame ℰ =  blame ([ ℰ ]⦅ _⊕_ ⦆ M)
... | step (ξ ℰ L↦L′)
    =  step (ξ ([ ℰ ]⦅ _⊕_ ⦆ M) L↦L′)
... | pending ℰ e v ¬e//ℰ
    =  pending ([ ℰ ]⦅ _⊕_ ⦆ M) e v ¬e//ℰ
... | done ($ k) with progress M
...     | done ($ k′) =  step (ξ □ δ)
...     | blame ℰ =  blame (($ k) ⦅ _⊕_ ⦆[ ℰ ])
...     | step (ξ ℰ M↦M′)
        =  step (ξ (($ k) ⦅ _⊕_ ⦆[ ℰ ]) M↦M′)
...     | pending ℰ e v ¬e//ℰ
        =  pending (($ k) ⦅ _⊕_ ⦆[ ℰ ]) e v ¬e//ℰ
```

A box constructor reduces its argument, and a boxed value is a value.
```
progress (M ⇑ g) with progress M
... | done v =  done (v ⇑ g)
... | blame ℰ =  blame ([ ℰ ]⇑ g)
... | step (ξ ℰ M↦M′)
    =  step (ξ ([ ℰ ]⇑ g) M↦M′)
... | pending ℰ e v ¬e//ℰ
    =  pending ([ ℰ ]⇑ g) e v ¬e//ℰ
```

For casts, we also try to reduce the term under the cast.
`blame` and `step` are wrapped by congruence.
```
progress (cast ±p M) with progress M
... | blame ℰ         =  blame (`cast ±p [ ℰ ])
... | step (ξ ℰ M↦M′)
    =  step (ξ (`cast ±p [ ℰ ]) M↦M′)
```

When a computation under a cast performs an operation `e`,
the effect cast validates that the operation is expected,
\ie{} it checks whether `e` is a member of the effect `F`
at that point. If it is (`yes`), then `e` remains unhandled.
If `e` is not allowed (`no`), then blame is raised by `blameᵉ`.
```
progress (cast {Q = ⟨ F ⟩ _} ±p M)
    | pending {e = e} ℰ e∈E v ¬e//ℰ
      with e ∈☆? F
...   | yes e∈F
      = pending (`cast ±p [ ℰ ]) e∈E v
          (¬handled-cast {±p = ±p} ℰ e∈F ¬e//ℰ)
...   | no ¬∈
      = step (ξ □ (blameᵉ ¬∈ ¬e//ℰ v refl))
```

Finally, when a cast is applied to a value, we apply the lemma `progress±`
that we proved earlier.
```
progress (cast ±p M) 
    | done v
        with progress± v ±p
...     | _ , V⟨±p⟩↦N                        = step (ξ □ V⟨±p⟩↦N)
```

Before pending an operation, we reduce its argument.
Once it is a value, the operation is `pending`.
```
progress (perform- e M eq) with progress M
... | blame ℰ = blame (″perform e [ ℰ ] eq)
... | step (ξ ℰ M↦M′)
    = step (ξ (″perform e [ ℰ ] eq) M↦M′)
... | pending ℰ e′∈E′ v ¬e′//ℰ
    = pending (″perform e [ ℰ ] eq) e′∈E′ v ¬e′//ℰ
... | done v with eq
...   | refl = pending □ e v (λ())
```

A handler extends `done` computations with its return clause and intercepts
`pending` operations with the relevant operation clause, if any,
and forwards unhandled operations to outer handlers.
```
progress (handle H M) with progress M
... | blame ℰ = blame (′handle H [ ℰ ])
... | step (ξ ℰ M↦M′)
    = step (ξ (′handle H [ ℰ ]) M↦M′)
... | done v = step (ξ □ (handle-value v))
... | pending {e = e} ℰ e∈E v ¬e//ℰ
      with e ∈? Hooks H in eq
...   | yes e∈H
      = step (ξ □ (handle-perform v ¬e//ℰ eq))
...   | no ¬e∈H
      = pending (′handle H [ ℰ ]) e∈E v
          (¬handled-handle {H = H} ℰ ¬e∈H ¬e//ℰ)
```

## Evaluation

The `progress` function computes a single reduction step.
It must be iterated to run a computation to its conclusion.

Computations may run forever. We ensure that the evaluation process terminates
by limiting it to a finite number of steps, so that it can be defined in Agda.
*Gas* is this bound on the number of reduction steps.
```
record Gas : Set where
  constructor gas
  field
    amount : ℕ
```
When our evaluator returns a term `N`, it will either give evidence that
`N` is a value, or indicate that blame occurred, or an operation was unhandled,
or it ran out of gas.
```
data Finished {P} : (∅ ⊢ P) → Set where

  done : ∀ {N : ∅ ⊢ P}
    → Value N
      ----------
    → Finished N

  blame : ∀ {Q}
    → (E : Frame ∅ Q P)
      ---------------------
    → Finished (E ⟦ blame ⟧)

  pending : ∀ {e V ℰ}
    → (e∈E : e ∈☆ E)
    → Value V
    → (e//ℰ : ¬ handled e ℰ)
      ------------------------------
    → Finished (ℰ ⟦ perform e∈E V ⟧)

  out-of-gas : {N : ∅ ⊢ P}
      ----------
    → Finished N
```
Given a term `L` of type `A`, the evaluator will, for some `N`, return
a reduction sequence from `L` to `N` and an indication of whether
reduction finished:
```
data Steps {A} : ∅ ⊢ A → Set where

  steps : {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L
```
The evaluator takes gas and a term and returns the corresponding steps:
```
eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
    -----------
  → Steps L
eval (gas zero) L     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L
    with progress L
... | done v          = steps (L ∎) (done v)
... | blame E         = steps (L ∎) (blame E)
... | pending ℰ e v ¬e//ℰ
    =  steps (L ∎) (pending e v ¬e//ℰ)
... | step {L} {M} L—→M
    with eval (gas m) M
... | steps M—↠N fin  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
```

## Type erasure

As a simple example, we consider two encodings of the
term `inc = (λ x → x + 1)`: one typed, one untyped. 

The `Static` predicate characterizes terms that
make no use of dynamism: they contain no casts.

```
data Static {Γ E} : (Γ ⊢ ⟨ E ⟩ A) → Set where

  `_ :
      (x : Γ ∋ A)
      ------------
    → Static (` x)

  ƛ_ : ∀ {F} {N : Γ ▷ A ⊢ ⟨ F ⟩ B}
    → Static N
      ------------
    → Static (ƛ N)

  _·_ :
      {L : Γ ⊢ ⟨ E ⟩ (A ⇒ ⟨ E ⟩ B)}
      {M : Γ ⊢ ⟨ E ⟩ A}
    → Static L
    → Static M
      --------------
    → Static (L · M)

  $_ : ∀ {ι}
    → (k : rep ι)
      -------------------
    → Static ($ k)

  _⦅_⦆_ : ∀ {ι ι′ ι″}
      {M : Γ ⊢ ⟨ E ⟩ ($ ι)}
      {N : Γ ⊢ ⟨ E ⟩ ($ ι′)}
    → Static M
    → (_⊕_ : rep ι → rep ι′ → rep ι″)
    → Static N
      --------------------
    → Static (M ⦅ _⊕_ ⦆ N)

static : ∀ {M : Γ ⊢ P}
  → (m : Static M)
    -------------
  → Γ ⊢ P
static {M = M} m  =  M
```

(TODO: handlers)

On the other end of the spectrum, we can embed untyped
lambda-calculus terms as cast-calculus terms of type `★`,
using the following constructs. Lambda abstractions are upcast to `★`,
applications downcast functions from `★` to `★ ⇒ ★`,
and primitive operators downcast their arguments and upcast the result.


```
infix 6 _≤★

pattern  _≤★ ι   =  id ⇑ ($ ι)
pattern  ★⇒★≤★   =  id ⇑ ★⇒★

infix  6 _·★_
infix  6 _⦅_⦆★_
infix  8 $★_

pattern  ƛ★_ N
  =  cast (+ ⟨ id ⟩ ★⇒★≤★) (ƛ N)
pattern  _·★_ L M
  =  (cast (- ⟨ id ⟩ ★⇒★≤★) L) · M
pattern  $★_ {ι = ι} k
  =  $ k ⇑ $ ι
pattern  _⦅_⦆★_ {ι = ι} {ι′} {ι″} M _⊕_ N
  =  cast (+ ⟨ id ⟩ (ι″ ≤★))
     ( cast (- ⟨ id ⟩ (ι ≤★)) M
       ⦅ _⊕_ ⦆
       cast (- ⟨ id ⟩ (ι′ ≤★)) N) 
```

The following functions define the embedding of a static term
viewed as an untyped term.

```
⌈_⌉ᴳ : Context → Context
⌈ ∅ ⌉ᴳ = ∅
⌈ Γ ▷ A ⌉ᴳ = ⌈ Γ ⌉ᴳ ▷ ★

⌈_⌉ˣ : (Γ ∋ A) → (⌈ Γ ⌉ᴳ ∋ ★)
⌈ Z ⌉ˣ          = Z
⌈ S x ⌉ˣ        = S ⌈ x ⌉ˣ

⌈_⌉ : {M : Γ ⊢ ⟨ E ⟩ A}
  → Static M
  → ⌈ Γ ⌉ᴳ ⊢ ⟨ ☆ ⟩ ★
⌈ ` x ⌉          =  ` ⌈ x ⌉ˣ
⌈ ƛ N ⌉          =  ƛ★ ⌈ N ⌉
⌈ L · M ⌉        =  ⌈ L ⌉ ·★ ⌈ M ⌉
⌈ $ k ⌉          =  $★ k
⌈ M ⦅ _⊕_ ⦆ N ⌉  =  ⌈ M ⌉ ⦅ _⊕_ ⦆★ ⌈ N ⌉
```

## Examples {#progress-examples}

The following abbreviations cause Agda to produce more readable output
when using `eval`.  In particular, the specialised `$ℕ★_`, `$𝔹★_`, and
`_⦅_⦆ℕ★_` lead to more readable results than the generic `$★_` and
`_⦅_⦆★_`.  After the output is produced, rewriting `ℕ★` and `𝔹★`
yields the more generic operators, which are fine for input.

```
pattern  $ℕ      =  $ ′ℕ
pattern  $𝔹      =  $ ′𝔹
pattern  ℕ≤★     =  id ⇑ $ℕ
pattern  𝔹≤★     =  id ⇑ $𝔹
ℕ⇒ℕ≤★' : $ℕ ⇒ ⟨ ε ⟩ $ℕ ≤ ★
ℕ⇒ℕ≤★' =  ℕ≤★ ⇒ ⟨ E≤☆ ⟩ ℕ≤★ ⇑ ★⇒★

pattern ε≤☆ = ¡≤☆ {E = []}

pattern  ℕ⇒ℕ≤★   =  ℕ≤★ ⇒ ⟨ ¡≤☆ ⟩ ℕ≤★ ⇑ ★⇒★

infix  6 _⦅_⦆ℕ★_
infix  8 $ℕ★_
infix  8 $𝔹★_

pattern  $ℕ★_ k          =  $ k ⇑ $ℕ
pattern  $𝔹★_ k          =  $ k ⇑ $𝔹
pattern  _⦅_⦆ℕ★_ M _⊕_ N
  =  cast (+ ⟨ id ⟩ ℕ≤★)
     ( cast (- ⟨ id ⟩ ℕ≤★) M
       ⦅ _⊕_ ⦆
       cast (- ⟨ id ⟩ ℕ≤★) N)

inc     :  ∅ ⊢ ⟨ ε ⟩ $ℕ ⇒ ⟨ ε ⟩ $ℕ
inc     =  ƛ (` Z ⦅ _+_ ⦆ $ 1)

Inc     :  Static inc
Inc     =  ƛ (` Z ⦅ _+_ ⦆ $ 1)

inc★    :  ∅ ⊢ ⟨ ☆ ⟩ ★
inc★    =  ⌈ Inc ⌉

inc★′   :  ∅ ⊢ ⟨ ☆ ⟩ ★
inc★′   =  cast (+ ⟨ ≤☆ ⟩ ℕ⇒ℕ≤★) inc
```

The following are reductions of the statically typed `inc` and the dynamically
typed `inc★`, both applied to the constant `2`.

```
inc2—↠3  : inc · ($ 2) —↠ $ 3
inc2—↠3  =
  begin
    (ƛ (` Z ⦅ _+_ ⦆ $ 1)) · $ 2
  —→⟨ ξ □ (β ($ 2)) ⟩
    $ 2 ⦅ _+_ ⦆ $ 1
  —→⟨ ξ □ δ ⟩ $ 3
  ∎
```

```
inc★2★—↠3★  : inc★ ·★ ($★ 2) —↠ $★ 3
```

```
inc★2★—↠3★  =
  begin
    (ƛ★ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ·★ $ℕ★ 2
  —→⟨ ξ ([ `cast (- ⟨ id ⟩ ★⇒★≤★)
                 [ □ ]
         ]· $ℕ★ 2)
        (expand (ƛ _) ★⇒★) ⟩
    (cast (+ ⟨ id ⟩ id)
          (ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ⇑ ★⇒★)
      ·★ $ℕ★ 2
  —→⟨ ξ ([ `cast (- ⟨ id ⟩ ★⇒★≤★)
                 [ [ □ ]⇑ ★⇒★ ]
         ]· $ℕ★ 2)
        (ident refl (ƛ _)) ⟩
    ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ⇑ ★⇒★)
      ·★ $ℕ★ 2
  —→⟨ ξ ([ □ ]· $ℕ★ 2) (collapse (ƛ _) ★⇒★) ⟩
    (cast (- ⟨ id ⟩ id)
          (ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)))
      · $ℕ★ 2
  —→⟨ ξ ([ □ ]· $ℕ★ 2) (ident refl (ƛ _)) ⟩
    (ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) · $ℕ★ 2
  —→⟨ ξ □ (β ($ℕ★ 2)) ⟩
    $ℕ★ 2 ⦅ _+_ ⦆ℕ★ $ℕ★ 1
  —→⟨ ξ (`cast (+ ⟨ id ⟩ ℕ≤★) [ [ □ ]⦅ _+_ ⦆
            cast (- ⟨ id ⟩ ℕ≤★) ($ℕ★ 1) ])
        (collapse ($ 2) $ℕ) ⟩
    cast (+ ⟨ id ⟩ ℕ≤★)
         ( cast (- ⟨ id ⟩ id) ($ 2)
           ⦅ _+_ ⦆
           cast (- ⟨ id ⟩ ℕ≤★) ($ℕ★ 1))
  —→⟨ ξ (`cast (+ ⟨ id ⟩ ℕ≤★) [ [ □ ]⦅ _+_ ⦆
            cast (- ⟨ id ⟩ ℕ≤★) ($ℕ★ 1) ])
        (ident refl ($ 2)) ⟩
    cast (+ ⟨ id ⟩ ℕ≤★)
         ($ 2 ⦅ _+_ ⦆
          cast (- ⟨ id ⟩ ℕ≤★) ($ℕ★ 1))
  —→⟨ ξ (`cast (+ ⟨ id ⟩ ℕ≤★)
               [ $ 2 ⦅ _+_ ⦆[ □ ] ])
        (collapse ($ 1) $ℕ) ⟩
    cast (+ ⟨ id ⟩ ℕ≤★)
         ($ 2 ⦅ _+_ ⦆
          cast (- ⟨ id ⟩ id) ($ 1))
  —→⟨ ξ (`cast (+ ⟨ id ⟩ ℕ≤★)
               [ $ 2 ⦅ _+_ ⦆[ □ ] ])
        (ident refl ($ 1)) ⟩
    cast (+ ⟨ id ⟩ ℕ≤★) ($ 2 ⦅ _+_ ⦆ $ 1)
  —→⟨ ξ (`cast (+ ⟨ id ⟩ ℕ≤★) [ □ ]) δ ⟩
    cast (+ ⟨ id ⟩ ℕ≤★) ($ 3)
  —→⟨ ξ □ (expand ($ 3) $ℕ) ⟩
    cast (+ ⟨ id ⟩ id) ($ 3) ⇑ $ℕ
  —→⟨ ξ ([ □ ]⇑ $ℕ) (ident refl ($ 3)) ⟩
    $ℕ★ 3
  ∎
```

\iffalse
```
{- TODO
inc★′2★—↠3★  : inc★′ ·★ ($★ 2) —↠ $★ 3
inc★′2★—↠3★  =
  begin
    ((ƛ (` Z ⦅ _+_ ⦆ $ 1)) ▷⟨ + E≤☆ ⟩ ▷ (+ ℕ⇒ℕ≤★)) ·★ $ℕ★ 2
  —→⟨ ξ ([ [ [ □ ]▷ (+ ℕ⇒ℕ≤★) ]▷ (- ★⇒★≤★) ]· $ℕ★ 2) (castᵉ-value (ƛ _)) ⟩
    ((ƛ (` Z ⦅ _+_ ⦆ $ 1)) ▷ (+ ℕ⇒ℕ≤★)) ·★ $ℕ★ 2
  —→⟨ ξ ([ [ □ ]▷ (- ★⇒★≤★) ]· $ℕ★ 2) (expand (ƛ _) ★⇒★) ⟩
    ((ƛ (` Z ⦅ _+_ ⦆ $ 1)) ▷ (+ ℕ≤★ ⇒ ⟨ E≤☆ ⟩ ℕ≤★) ⇑ ★⇒★) ·★ $ℕ★ 2
  —→⟨ ξ ([ [ [ □ ]⇑ ★⇒★ ]▷ (- ★⇒★≤★) ]· $ℕ★ 2) (wrap refl) ⟩
    let f = ƛ ((ƛ (` Z ⦅ _+_ ⦆ $ 1)) · (` Z ▷ (- ℕ≤★)) ▷⟨ + E≤☆ ⟩ ▷ (+ ℕ≤★)) in
    (f ⇑ ★⇒★) ·★ $ℕ★ 2
  —→⟨ ξ ([ □ ]· $ℕ★ 2) (collapse (ƛ _) ★⇒★) ⟩
    (f ▷ (- id)) · $ℕ★ 2
  —→⟨ ξ ([ □ ]· $ℕ★ 2) (ident refl (ƛ _)) ⟩
    f · $ℕ★ 2
  —→⟨ ξ □ (β ($ℕ★ 2)) ⟩
    (ƛ (` Z ⦅ _+_ ⦆ $ 1)) · ($ℕ★ 2 ▷ (- ℕ≤★)) ▷⟨ + E≤☆ ⟩ ▷ (+ ℕ≤★)
  —→⟨ ξ ([ [ (ƛ (` Z ⦅ _+_ ⦆ $ 1)) ·[ □ ] ]▷⟨ + E≤☆ ⟩ ]▷ (+ ℕ≤★)) (collapse ($ 2) $ℕ) ⟩
    (ƛ (` Z ⦅ _+_ ⦆ $ 1)) · ($ 2 ▷ (- id)) ▷⟨ + E≤☆ ⟩ ▷ (+ ℕ≤★)
  —→⟨ ξ ([ [ (ƛ (` Z ⦅ _+_ ⦆ $ 1)) ·[ □ ] ]▷⟨ + E≤☆ ⟩ ]▷ (+ ℕ≤★)) (ident refl ($ 2)) ⟩
    (ƛ (` Z ⦅ _+_ ⦆ $ 1)) · $ 2 ▷⟨ + E≤☆ ⟩ ▷ (+ ℕ≤★)
  —→⟨ ξ ([ [ □ ]▷⟨ + E≤☆ ⟩ ]▷ (+ ℕ≤★)) (β ($ 2)) ⟩
    $ 2 ⦅ _+_ ⦆ $ 1 ▷⟨ + E≤☆ ⟩ ▷ (+ ℕ≤★)
  —→⟨ ξ ([ [ □ ]▷⟨ + E≤☆ ⟩ ]▷ (+ ℕ≤★)) δ ⟩
    $ 3 ▷⟨ + E≤☆ ⟩ ▷ (+ ℕ≤★)
  —→⟨ ξ ([ □ ]▷ (+ ℕ≤★)) (castᵉ-value ($ 3)) ⟩
    $ 3 ▷ (+ ℕ≤★)
  —→⟨ ξ □ (expand ($ 3) $ℕ) ⟩
    $ 3 ▷ (+ id) ⇑ $ℕ
  —→⟨ ξ ([ □ ]⇑ $ℕ) (ident refl ($ 3)) ⟩
    $ℕ★ 3
  ∎

inc★true★—↠blame : inc★ ·★ ($★ true) —↠
  ([ [ □ ]⦅ _+_ ⦆ ($ℕ★ 1 ▷ (- ℕ≤★)) ]▷ (+ ℕ≤★)) ⟦ blame ⟧
inc★true★—↠blame =
  begin
    (ƛ★ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ·★ $𝔹★ true
  —→⟨ ξ ([ [ □ ]▷ (- ★⇒★≤★) ]· $𝔹★ true) (expand (ƛ _) ★⇒★) ⟩
    ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ▷ (+ id) ⇑ ★⇒★) ·★ $𝔹★ true
  —→⟨ ξ ([ [ [ □ ]⇑ ★⇒★ ]▷ (- ★⇒★≤★) ]· $𝔹★ true) (ident refl (ƛ _)) ⟩
    ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ⇑ ★⇒★) ·★ $𝔹★ true
  —→⟨ ξ ([ □ ]· $𝔹★ true) (collapse (ƛ _) ★⇒★) ⟩
    ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ▷ (- id)) · $𝔹★ true
  —→⟨ ξ ([ □ ]· $𝔹★ true) (ident refl (ƛ _)) ⟩
    (ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) · $𝔹★ true
  —→⟨ ξ □ (β ($𝔹★ true)) ⟩
    $𝔹★ true ⦅ _+_ ⦆ℕ★ $ℕ★ 1
  —→⟨ ξ ([ [ □ ]⦅ _+_ ⦆ ($ℕ★ 1 ▷ (- ℕ≤★)) ]▷ (+ ℕ≤★)) (collide ($ true) $𝔹 $ℕ (λ())) ⟩
    blame ⦅ _+_ ⦆ ($ℕ★ 1 ▷ (- ℕ≤★)) ▷ (+ ℕ≤★)
  ∎
  -}
```
\fi
