# Operational Semantics

```
module Progress where

open import Utils
open import Type
open import Core

import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any.Properties as Any
```

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

```
data Frame (Γ : Context) (C : Typeᶜ) : Typeᶜ → Set where

  □ : Frame Γ C C

  [_]·_ : ∀ {E A B}
    →  (ℰ : Frame Γ C (⟨ E ⟩ (A ⇒ ⟨ E ⟩ B)))
    →  (M : Γ ⊢ ⟨ E ⟩ A)
       ---------------
    →  Frame Γ C (⟨ E ⟩ B)

  _·[_] : ∀ {E A B}{V : Γ ⊢ ⟨ E ⟩ (A ⇒ ⟨ E ⟩ B)}
    →  (v : Value V)
    →  (ℰ : Frame Γ C (⟨ E ⟩ A))
       ----------------
    →  Frame Γ C (⟨ E ⟩ B)

  [_]⦅_⦆_ : ∀ {E ι ι′ ι″}
    →  (ℰ : Frame Γ C (⟨ E ⟩ ($ ι)))
    →  (_⊕_ : rep ι → rep ι′ → rep ι″)
    →  (N : Γ ⊢ ⟨ E ⟩ ($ ι′))
       ------------------
    →  Frame Γ C (⟨ E ⟩ ($ ι″))

  _⦅_⦆[_] : ∀ {E ι ι′ ι″}{V : Γ ⊢ ⟨ E ⟩ $ ι}
    →  (v : Value V)
    →  (_⊕_ : rep ι → rep ι′ → rep ι″)
    →  (ℰ : Frame Γ C (⟨ E ⟩ ($ ι′)))
       -------------------
    →  Frame Γ C (⟨ E ⟩ ($ ι″))

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
    →  Γ ⊢ P ➡ Q
    →  Frame Γ C P
       -----------
    →  Frame Γ C Q

pattern ′perform_[_] e ℰ = ″perform e [ ℰ ] refl
```

The plug function inserts an expression into the hole of a frame.
```
_⟦_⟧ : ∀{Γ A B} → Frame Γ A B → Γ ⊢ A → Γ ⊢ B
□ ⟦ M ⟧                 =  M
([ ℰ ]· M) ⟦ L ⟧        =  ℰ ⟦ L ⟧ · M
(v ·[ ℰ ]) ⟦ M ⟧        =  value v · ℰ ⟦ M ⟧
([ ℰ ]⦅ _⊕_ ⦆ N) ⟦ M ⟧  =  ℰ ⟦ M ⟧ ⦅ _⊕_ ⦆ N
(v ⦅ _⊕_ ⦆[ ℰ ]) ⟦ N ⟧  =  value v ⦅ _⊕_ ⦆ ℰ ⟦ N ⟧
([ ℰ ]⇑ g) ⟦ M ⟧        =  ℰ ⟦ M ⟧ ⇑ g
(`cast ±p [ ℰ ]) ⟦ M ⟧  =  cast ±p (ℰ ⟦ M ⟧)
(″perform e∈E [ ℰ ] eq) ⟦ M ⟧ = perform- e∈E (ℰ ⟦ M ⟧) eq
(′handle H [ ℰ ]) ⟦ M ⟧ = handle H (ℰ ⟦ M ⟧)
```

Composition of two frames
```
_∘∘_ : ∀{Γ A B C} → Frame Γ B C → Frame Γ A B → Frame Γ A C
□ ∘∘ 𝐹                 =  𝐹
([ ℰ ]· M) ∘∘ 𝐹        =  [ ℰ ∘∘ 𝐹 ]· M
(v ·[ ℰ ]) ∘∘ 𝐹        =  v ·[ ℰ ∘∘ 𝐹 ]
([ ℰ ]⦅ _⊕_ ⦆ N) ∘∘ 𝐹  =  [ ℰ ∘∘ 𝐹 ]⦅ _⊕_ ⦆ N
(v ⦅ _⊕_ ⦆[ ℰ ]) ∘∘ 𝐹  =  v ⦅ _⊕_ ⦆[ ℰ ∘∘ 𝐹 ]
([ ℰ ]⇑ g) ∘∘ 𝐹        =  [ ℰ ∘∘ 𝐹 ]⇑ g
(`cast ±p [ ℰ ]) ∘∘ 𝐹     =  `cast ±p [ ℰ ∘∘ 𝐹 ]
(″perform e∈E [ ℰ ] eq) ∘∘ 𝐹 = ″perform e∈E [ ℰ ∘∘ 𝐹 ] eq
(′handle H [ ℰ ]) ∘∘ 𝐹  =  ′handle H [ ℰ ∘∘ 𝐹 ]
```

Composition and plugging
```
∘∘-lemma : ∀ {Γ A B C}
  → (ℰ : Frame Γ B C)
  → (𝐹 : Frame Γ A B)
  → (M : Γ ⊢ A)
    -----------------------------
  → ℰ ⟦ 𝐹 ⟦ M ⟧ ⟧ ≡ (ℰ ∘∘ 𝐹) ⟦ M ⟧
∘∘-lemma □ 𝐹 M                                         =  refl
∘∘-lemma ([ ℰ ]· M₁) 𝐹 M       rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
∘∘-lemma (v ·[ ℰ ]) 𝐹 M        rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
∘∘-lemma ([ ℰ ]⦅ _⊕_ ⦆ N) 𝐹 M  rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
∘∘-lemma (v ⦅ _⊕_ ⦆[ ℰ ]) 𝐹 M  rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
∘∘-lemma ([ ℰ ]⇑ g) 𝐹 M        rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
∘∘-lemma (`cast ±p [ ℰ ]) 𝐹 M  rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
∘∘-lemma (″perform e∈E [ ℰ ] eq) 𝐹 M rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
∘∘-lemma (′handle H [ ℰ ]) 𝐹 M rewrite ∘∘-lemma ℰ 𝐹 M  =  refl
```

```
renᶠ : ∀ {Γ Δ P Q} → Γ →ᴿ Δ → Frame Γ P Q → Frame Δ P Q
renᶠ ρ □ = □
renᶠ ρ ([ ℰ ]· M) = [ renᶠ ρ ℰ ]· ren ρ M
renᶠ ρ (v ·[ ℰ ]) = ren-val ρ v ·[ renᶠ ρ ℰ ]
renᶠ ρ ([ ℰ ]⦅ f ⦆ M) = [ renᶠ ρ ℰ ]⦅ f ⦆ ren ρ M
renᶠ ρ (v ⦅ f ⦆[ ℰ ]) = ren-val ρ v ⦅ f ⦆[ renᶠ ρ ℰ ]
renᶠ ρ ([ ℰ ]⇑ g) = [ renᶠ ρ ℰ ]⇑ g
renᶠ ρ (`cast ±p [ ℰ ]) = `cast ±p [ renᶠ ρ ℰ ]
renᶠ ρ (″perform e∈E [ ℰ ] eq) = ″perform e∈E [ renᶠ ρ ℰ ] eq
renᶠ ρ (′handle H [ ℰ ]) = ′handle (renʰ ρ H) [ renᶠ ρ ℰ ]

liftᶠ : ∀ {Γ P Q A} → Frame Γ P Q → Frame (Γ ▷ A) P Q
liftᶠ = renᶠ S_

liftʰ : ∀ {Γ P Q A} → Γ ⊢ P ➡ Q → Γ ▷ A ⊢ P ➡ Q
liftʰ = renʰ S_
```

Decomposing a cast
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
```

```
=>ᶜ-effects : ∀ {P Q} (±q : P =>ᶜ Q) → Typeᶜ.effects P =>ᵉ Typeᶜ.effects Q
=>ᶜ-effects (+ ⟨ p ⟩ _) = + p
=>ᶜ-effects (- ⟨ p ⟩ _) = - p

=>ᶜ-returns : ∀ {P Q} (±q : P =>ᶜ Q) → Typeᶜ.returns P => Typeᶜ.returns Q
=>ᶜ-returns (+ ⟨ _ ⟩ q) = + q
=>ᶜ-returns (- ⟨ _ ⟩ q) = - q
```

```
splitᶜ : ∀ {E F A B}
  →  (⟨ E ⟩ A) =>ᶜ (⟨ F ⟩ B)
     -----------------------
  →  A ==> B
splitᶜ = split ∘ =>ᶜ-returns
```

```
private
  variable
    A A′ B G : Type
    P P′ Q Q′ : Typeᶜ
    E E′ F : Effect
    Γ : Context
```

## Reduction

The effect row in the codomain of the cast. 
```
cast-effect : {P Q : Typeᶜ} → P =>ᶜ Q → Effect
cast-effect {Q = ⟨ E ⟩ B} _ = E
```

`handled e ℰ` means that the operation `e` is handled by the evaluation context `ℰ`:
either `ℰ` contains a handler where `e` is one of its hooks, or `ℰ` contains a cast
where `e` is not allowed by the codomain of the cast.
```
handled : ∀ e → Frame Γ P Q → Set
handled e □ = ⊥
handled e (′handle H [ ℰ ]) = e ∈ H .Hooks ⊎ handled e ℰ
handled {Q = ⟨ E ⟩ _} e (`cast ±p [ ℰ ]) = (¬ e ∈☆ E) ⊎ handled e ℰ  -- ±p : P => ⟨ E ⟩ B
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
  ∀ (e : Op) → e ∈☆ Typeᶜ.effects P → ¬ handled e ℰ₀
upcast-safety (⟨ ¡≤☆ ⟩ _) e e∈E (inj₁ ¬e∈☆) = ¬e∈☆ ☆
upcast-safety (⟨ id  ⟩ _) e e∈E (inj₁ ¬e∈E) = ¬e∈E e∈E
```

```
¬handled-cast : ∀ {e} {±p : (⟨ E ⟩ A) =>ᶜ (⟨ F ⟩ B)} (ℰ : Frame Γ P (⟨ E ⟩ A))
  → e ∈☆ F
  → ¬ handled e ℰ
    -------------------------
  → ¬ handled e (`cast ±p [ ℰ ])
¬handled-cast ℰ e∈F ¬e//ℰ (inj₁ ¬e∈F) = ¬e∈F e∈F
¬handled-cast ℰ e∈F ¬e//ℰ (inj₂ e//ℰ) = ¬e//ℰ e//ℰ

¬handled-handle : ∀ {e} {H : Γ ⊢ P ➡ Q} (ℰ : Frame Γ P′ P)
  → ¬ e ∈ Hooks H
  → ¬ handled e ℰ
    -----------------------------
  → ¬ handled e (′handle H [ ℰ ])
¬handled-handle ℰ ¬e∈H ¬e//ℰ (inj₁ e∈H) = ¬e∈H e∈H
¬handled-handle ℰ ¬e∈H ¬e//ℰ (inj₂ e//ℰ) = ¬e//ℰ e//ℰ

∈☆-++☆ʳ : ∀ {e Eh} → e ∈☆ E → e ∈☆ (Eh ++☆ E)
∈☆-++☆ʳ {Eh = Eh} (¡ e∈E) = ¡ (Any.++⁺ʳ Eh e∈E)
∈☆-++☆ʳ ☆ = ☆

∈☆-++☆⁻ : ∀ {e Eh} → e ∈☆ (Eh ++☆ E) → e ∈ Eh ⊎ e ∈☆ E
∈☆-++☆⁻ {E = ☆} _ = inj₂ ☆
∈☆-++☆⁻ {E = ¡ _} {Eh = Eh} (¡ e∈++) with Any.++⁻ Eh e∈++
... | inj₁ e∈Eh = inj₁ e∈Eh
... | inj₂ e∈E = inj₂ (¡ e∈E)

¬∈-handler : ∀ {e} (H : Γ ⊢ ⟨ E ⟩ A ➡ ⟨ F ⟩ B) → e ∈☆ E → ¬ e ∈ H .Hooks → e ∈☆ F
¬∈-handler H e∈E ¬e∈H rewrite Hooks-handled H with ∈☆-++☆⁻ e∈E
... | inj₁ e∈H = ⊥-elim (¬e∈H e∈H)
... | inj₂ e∈F = e∈F

¬¬-dec : ∀ {P : Set} → Dec P → ¬ ¬ P → P
¬¬-dec (yes p) _ = p
¬¬-dec (no ¬p) ¬¬p = ⊥-elim (¬¬p ¬p)

¬handled-∈ : ∀ {e} (ℰ : Frame Γ (⟨ E ⟩ A) (⟨ F ⟩ B)) → ¬ handled e ℰ → e ∈☆ E → e ∈☆ F
¬handled-∈ □ _ e∈E = e∈E
¬handled-∈ ([ ℰ ]· M) ¬e//ℰ = ¬handled-∈ ℰ ¬e//ℰ
¬handled-∈ (v ·[ ℰ ]) ¬e//ℰ = ¬handled-∈ ℰ ¬e//ℰ
¬handled-∈ ([ ℰ ]⦅ _⊕_ ⦆ N) ¬e//ℰ = ¬handled-∈ ℰ ¬e//ℰ
¬handled-∈ (v ⦅ _⊕_ ⦆[ ℰ ]) ¬e//ℰ = ¬handled-∈ ℰ ¬e//ℰ
¬handled-∈ ([ ℰ ]⇑ g) ¬e//ℰ = ¬handled-∈ ℰ ¬e//ℰ
¬handled-∈ (`cast ±p [ ℰ ]) ¬e//ℰ e∈E = ¬¬-dec (_ ∈☆? _) (¬e//ℰ ∘ inj₁)
¬handled-∈ (″perform e∈E [ ℰ ] x₁) ¬e//ℰ = ¬handled-∈ ℰ ¬e//ℰ
¬handled-∈ (′handle H [ ℰ ]) ¬e//ℰ e∈E = ¬∈-handler H (¬handled-∈ ℰ (¬e//ℰ ∘ inj₂) e∈E) (¬e//ℰ ∘ inj₁)
```

```
infix 2 _↦_ _—→_

pure± : (A′ => A) → (⟨ E ⟩ A′) =>ᶜ (⟨ E ⟩ A)
pure± (+ A≤) = + ⟨ id ⟩ A≤
pure± (- A≤) = - ⟨ id ⟩ A≤

ƛ-wrap : ∀ (∓s : A′ => A) (±t : P =>ᶜ P′) 
  → (∀ {E} → Γ ⊢ ⟨ E ⟩ (A ⇒ P)) → (∀ {E} → Γ ⊢ ⟨ E ⟩ (A′ ⇒ P′))
ƛ-wrap ∓s ±t M =
  ƛ cast ±t (lift M · (cast (pure± ∓s) (` Z)))

data _↦_ {Γ} : (_ _ : Γ ⊢ P) → Set where

  -- The substitution will put the value under different effects,
  -- the `value` function generalizes the effect of a value.
  β : ∀ {N : Γ ▷ A ⊢ ⟨ E ⟩ B} {W : Γ ⊢ ⟨ E ⟩ A}
    → (w : Value W)
      --------------------
    → (ƛ N) · W ↦ N [ gvalue w ]

  δ : ∀ {ι ι′ ι″} {_⊕_ : rep ι → rep ι′ → rep ι″} {k : rep ι} {k′ : rep ι′}
      --------------------------------------------
    → _⦅_⦆_ {Γ = Γ} {E = E} ($ k) _⊕_ ($ k′) ↦ $ (k ⊕ k′)

  ident : ∀ {V : Γ ⊢ ⟨ E ⟩ A} {±p : (⟨ E ⟩ A) =>ᶜ ⟨ F ⟩ A}
    → splitᶜ ±p ≡ id
    → (v : Value V)
      --------------
    → cast ±p V ↦ gvalue v

  wrap : {N : Γ ▷ A ⊢ P}
      {∓s : A′ => A} {±t : P =>ᶜ P′} {±p : (⟨ E ⟩ (A ⇒ P)) =>ᶜ ⟨ E′ ⟩ (A′ ⇒ P′)}
    → splitᶜ ±p ≡ ∓s ⇒ ±t
      ----------------------------------------------------
    → cast ±p (ƛ N) ↦ ƛ-wrap ∓s ±t (ƛ N)

  expand : ∀{V : Γ ⊢ ⟨ E ⟩ A} {p : A ≤ G} {E≤E′ : E ≤ᵉ E′}
    → Value V
    → (g : Ground G)
      -------------------------------
    → cast (+ ⟨ E≤E′ ⟩ (p ⇑ g)) V ↦ cast (+ ⟨ E≤E′ ⟩ p) V ⇑ g

  collapse : ∀ {V : Γ ⊢ ⟨ E ⟩ G} {p : A ≤ G} {E′≤E : E′ ≤ᵉ E}
    → Value V
    → (g : Ground G)
      --------------------------------
    → cast (- ⟨ E′≤E ⟩ (p ⇑ g)) (V ⇑ g) ↦ cast (- ⟨ E′≤E ⟩ p) V

  collide  : ∀{G H} {V : Γ ⊢ ⟨ E ⟩ G} {p : A ≤ H} {E′≤E : E′ ≤ᵉ E}
    → Value V
    → (g : Ground G)
    → (h : Ground H)
    → G ≢ H
      -----------------------------
    → cast (- ⟨ E′≤E ⟩ (p ⇑ h)) (V ⇑ g) ↦ blame

  castᵉ-blame : ∀ {e} {e∈E′ : e ∈☆ E′} {ℰ : Frame Γ (⟨ E′ ⟩ response e) (⟨ E ⟩ A)} {V} {M}
      {±p : ⟨ E ⟩ A =>ᶜ ⟨ F ⟩ B}
    → ¬ e ∈☆ F
    → ¬ handled e ℰ
    → Value V
    → M ≡ ℰ ⟦ perform e∈E′ V ⟧
      ---------------------------
    → cast ±p M ↦ blame

  handle-value : ∀ {H : Γ ⊢ P ➡ Q} {V}
    → (v : Value V)
      --------------
    → handle H V ↦ (H ._⊢_➡_.on-return [ gvalue v ])

  handle-perform : ∀ {e} {e∈E : e ∈☆ E} {H : Γ ⊢ P ➡ Q} {V ℰ e∈Hooks}
    → (v : Value V)
    → ¬ handled e ℰ                 -- ensures H is the first matching handler
    → (e ∈? Hooks H) ≡ yes e∈Hooks  -- ensures this is the first matching clause within H
                                    -- TODO: a more declarative reformulation?
    → handle H (ℰ ⟦ perform e∈E V ⟧)
      ↦ All.lookup (on-perform H) e∈Hooks
          [ ƛ (handle (liftʰ (liftʰ H)) (liftᶠ (liftᶠ ℰ) ⟦ ` Z ⟧)) ]
          [ gvalue v ]
    -- TODO: explain the order of these substitutions and why the 2 lifts

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξξ : ∀ {Γ A B} {M N : Γ ⊢ A} {M′ N′ : Γ ⊢ B}
    → ( ℰ : Frame Γ A B)
    → M′ ≡ ℰ ⟦ M ⟧
    → N′ ≡ ℰ ⟦ N ⟧
    → M ↦ N
      --------
    → M′ —→ N′
```

Notation
```
pattern ξ E M—→N = ξξ E refl refl M—→N
```

## Reflexive and transitive closure of reduction

```
infixr 1 _++↠_
infix  1 begin_
infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infixr 2 _—↠⟨_⟩_
infix  3 _∎

data _—↠_ : ∀{Γ A} → Γ ⊢ A → Γ ⊢ A → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A} → (M —↠ N) → (M —↠ N)
begin M—↠N = M—↠N
```

Convenience function to build a sequence of length one.
```
unit : ∀ {Γ A} {M N : Γ ⊢ A} → (M ↦ N) → (M —↠ N)
unit {M = M} {N = N} M↦N  =  M —→⟨ ξ □ M↦N ⟩ N ∎
```

Apply ξ to each element of a sequence
```
ξ* : ∀{Γ A B} {M N : Γ ⊢ A} → (E : Frame Γ A B) → M —↠ N → E ⟦ M ⟧ —↠ E ⟦ N ⟧
ξ* E (M ∎) = E ⟦ M ⟧ ∎
ξ* E (L —→⟨ ξξ {M = L′} {N = M′} F refl refl L′↦M′ ⟩ M—↠N)
  =  (E ⟦ L ⟧ —→⟨ ξξ (E ∘∘ F) (∘∘-lemma E F L′)
       (∘∘-lemma E F M′) L′↦M′ ⟩ (ξ* E M—↠N))
```

Concatenate two sequences.
```
_++↠_ : ∀ {Γ A} {L M N : Γ ⊢ A} → L —↠ M → M —↠ N → L —↠ N
(M ∎) ++↠ M—↠N                =  M—↠N
(L —→⟨ L—→M ⟩ M—↠N) ++↠ N—↠P  =  L —→⟨ L—→M ⟩ (M—↠N ++↠ N—↠P)
```

Alternative notation for sequence concatenation.
```
_—↠⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
  → L —↠ M
  → M —↠ N
    ---------
  → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N  =  L—↠M ++↠ M—↠N
```

## Irreducible terms

Values are irreducible.  The auxiliary definition rearranges the
order of the arguments because it works better for Agda.
```
value-irreducible : ∀ {Γ A} {V M : Γ ⊢ A} → Value V → ¬ (V —→ M)
value-irreducible v V—→M = nope V—→M v
   where
   nope : ∀ {Γ A} {V M : Γ ⊢ A} → V —→ M → Value V → ⊥
   nope (ξ □ (β x)) ()
   nope (ξ □ δ) ()
   nope (ξ □ (ident e v)) ()
   nope (ξ □ (wrap e)) ()
   nope (ξ □ (expand v g)) ()
   nope (ξ □ (collapse v g)) ()
   nope (ξ □ (collide v g h G≢H)) ()
   nope (ξ □ (castᵉ-blame ¬∈ e//ℰ v′ eq)) ()
   nope (ξ ([ E ]⇑ g) V—→M) (v ⇑ g)  =  nope (ξ E V—→M) v
   nope (ξξ (″perform _ [ _ ] _) refl _ _) ()
```

Variables are irreducible.
```
variable-irreducible : ∀ {x : Γ ∋ A} {N : Γ ⊢ ⟨ E ⟩ A}
    ------------
  → ¬ (` x —→ N)
variable-irreducible (ξξ □ refl _ ())
```

Boxes are irreducible (at the top level)
```
box-irreducible : ∀ {Γ G} {M : Γ ⊢ ⟨ E ⟩ G} {N : Γ ⊢ ⟨ E ⟩ ★}
  → (g : Ground G)
    --------------
  → ¬ (M ⇑ g ↦ N)
box-irreducible g ()
```

Blame is irreducible.
```
blame-irreducible : ∀ {M′ : Γ ⊢ P}  → ¬ (blame —→ M′)
blame-irreducible (ξ □ ())
```

```
unframe-blame : ∀ {M} (ℰ : Frame Γ P Q) → blame ≡ ℰ ⟦ M ⟧ → blame ≡ M
unframe-blame □ blame≡ = blame≡
```

## Progress

Every term that is well typed and closed is either
blame or a value or takes a reduction step.

```
data Progress {P} : (∅ ⊢ P) → Set where

  step : ∀ {M N : ∅ ⊢ P}
    → M —→ N
      ----------
    → Progress M

  done : ∀ {M : ∅ ⊢ P}
    → Value M
      ----------
    → Progress M

  blame : ∀ {Q}
   → (E : Frame ∅ Q P)
     ---------------------
   → Progress (E ⟦ blame ⟧)

  performing : ∀ {e} {V} ℰ
    → (e∈E : e ∈☆ E)
    → Value V
    → ¬ handled e ℰ
      ------------------
    → Progress (ℰ ⟦ perform e∈E V ⟧)

progress± : ∀ {V : ∅ ⊢ P}
  → (v : Value V)
  → (±p : P =>ᶜ Q)
    --------------------
  → ∃[ M ](cast ±p V ↦ M)
progress± v ±p with splitᶜ ±p in e
progress± v     _ | id                       =  _ , ident e v
progress± (ƛ _) _ | _ ⇒ _                    =  _ , wrap e
progress± v       (+ ⟨ _ ⟩ (_ ⇑ g)) | other  =  _ , expand v g
progress± (v ⇑ g) (- ⟨ _ ⟩ (_ ⇑ h)) | other
    with ground g ≡? ground h
... | yes refl rewrite uniqueG g h           =  _ , collapse v h
... | no  G≢H                                =  _ , collide v g h G≢H

progress :
    (M : ∅ ⊢ P)
    -----------
  → Progress M

progress (ƛ N)                           =  done (ƛ N)
progress (L · M) with progress L
... | blame ℰ                            =  blame ([ ℰ ]· M)
... | step (ξ ℰ L↦L′)                    =  step (ξ ([ ℰ ]· M) L↦L′)
... | performing ℰ e∈E v ¬e//ℰ           =  performing ([ ℰ ]· M) e∈E v ¬e//ℰ
... | done (ƛ N) with progress M
...     | blame ℰ                        =  blame ((ƛ N) ·[ ℰ ])
...     | step (ξ ℰ M↦M′)                =  step (ξ ((ƛ N) ·[ ℰ ]) M↦M′)
...     | performing ℰ e∈E v ¬e//ℰ       =  performing ((ƛ N) ·[ ℰ ]) e∈E v ¬e//ℰ
...     | done w                         =  step (ξ □ (β w))
progress ($ k)                           =  done ($ k)
progress (L ⦅ _⊕_ ⦆ M) with progress L
... | blame ℰ                            =  blame ([ ℰ ]⦅ _⊕_ ⦆ M)
... | step (ξ ℰ L↦L′)                    =  step (ξ ([ ℰ ]⦅ _⊕_ ⦆ M) L↦L′)
... | performing ℰ e∈E v ¬e//ℰ           =  performing ([ ℰ ]⦅ _⊕_ ⦆ M) e∈E v ¬e//ℰ
... | done ($ k) with progress M
...     | blame ℰ                        =  blame (($ k) ⦅ _⊕_ ⦆[ ℰ ])
...     | step (ξ ℰ M↦M′)                =  step (ξ (($ k) ⦅ _⊕_ ⦆[ ℰ ]) M↦M′)
...     | performing ℰ e∈E v ¬e//ℰ       =  performing (($ k) ⦅ _⊕_ ⦆[ ℰ ]) e∈E v ¬e//ℰ
...     | done ($ k′)                    =  step (ξ □ δ)
progress (M ⇑ g) with progress M
... | blame ℰ                            =  blame ([ ℰ ]⇑ g)
... | step (ξ ℰ M↦M′)                    =  step (ξ ([ ℰ ]⇑ g) M↦M′)
... | performing ℰ e∈E v ¬e//ℰ            =  performing ([ ℰ ]⇑ g) e∈E v ¬e//ℰ
... | done v                             =  done (v ⇑ g)
progress (cast ±p M) with progress M
... | blame ℰ           =  blame (`cast ±p [ ℰ ])
... | step (ξ ℰ M↦M′)   =  step (ξ (`cast ±p [ ℰ ]) M↦M′)
progress (cast {Q = ⟨ F ⟩ _} ±p M)
    | performing {e = e} ℰ e∈E v ¬e//ℰ
        with e ∈☆? F
...     | yes e∈F = performing (`cast ±p [ ℰ ]) e∈E v (¬handled-cast {±p = ±p} ℰ e∈F ¬e//ℰ)
...     | no  ¬∈  = step (ξ □ (castᵉ-blame ¬∈ ¬e//ℰ v refl))
progress (cast ±p M) 
    | done v
        with progress± v ±p
...     | _ , V⟨±p⟩↦N                        = step (ξ □ V⟨±p⟩↦N)
progress blame                           =  blame □
progress (perform- e∈E M eq) with progress M
... | blame ℰ                            = blame (″perform e∈E [ ℰ ] eq)
... | step (ξ ℰ M↦M′)                    = step (ξ (″perform e∈E [ ℰ ] eq) M↦M′)
... | performing ℰ e′∈E′ v ¬e′//ℰ        = performing (″perform e∈E [ ℰ ] eq) e′∈E′ v ¬e′//ℰ
... | done v with eq
...   | refl = performing □ e∈E v (λ())
progress (handle H M) with progress M
... | blame ℰ = blame (′handle H [ ℰ ])
... | step (ξ ℰ M↦M′) = step (ξ (′handle H [ ℰ ]) M↦M′)
... | done v = step (ξ □ (handle-value v))
... | performing {e = e} ℰ e∈E v ¬e//ℰ with e ∈? Hooks H in eq
...   | yes e∈H = step (ξ □ (handle-perform v ¬e//ℰ eq))
...   | no ¬e∈H = performing (′handle H [ ℰ ]) e∈E v (¬handled-handle {H = H} ℰ ¬e∈H ¬e//ℰ)
```


## Evaluation

Gas is specified by a natural number:
```
record Gas : Set where
  constructor gas
  field
    amount : ℕ
```
When our evaluator returns a term `N`, it will either give evidence that
`N` is a value, or indicate that blame occurred or it ran out of gas.
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

  performing : ∀ {e V ℰ}
    → (e∈E : e ∈☆ E)
    → Value V
    → (e//ℰ : ¬ handled e ℰ)
      ------------------------------
    → Finished (ℰ ⟦ perform e∈E V ⟧)

  out-of-gas : {N : ∅ ⊢ P}
      ----------
    → Finished N
```
Given a term `L` of type `A`, the ev aluator will, for some `N`, return
a reduction sequence from `L` to `N`  and an indication of whether
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
eval (gas zero) L          =  steps (L ∎) out-of-gas
eval (gas (suc m)) L
    with progress L
... | done v               =  steps (L ∎) (done v)
... | blame E              =  steps (L ∎) (blame E)
... | performing ℰ e∈E v ¬e//ℰ =  steps (L ∎) (performing e∈E v ¬e//ℰ)
... | step {L} {M} L—→M
    with eval (gas m) M
... | steps M—↠N fin       =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
```

## Type erasure

```
infix 6 _≤★

pattern  _≤★ ι   =  id ⇑ ($ ι)
pattern  ★⇒★≤★   =  id ⇑ ★⇒★

infix  6 _·★_
infix  6 _⦅_⦆★_
infix  8 $★_

pattern  ƛ★_ N          =  cast (+ ⟨ id ⟩ ★⇒★≤★) (ƛ N)
pattern  _·★_ L M       =  (cast (- ⟨ id ⟩ ★⇒★≤★) L) · M
pattern  $★_ {ι = ι} k  =  $ k ⇑ $ ι
pattern  _⦅_⦆★_ {ι = ι} {ι′} {ι″} M _⊕_ N
  =  cast (+ ⟨ id ⟩ (ι″ ≤★)) (cast (- ⟨ id ⟩ (ι ≤★)) M ⦅ _⊕_ ⦆ cast (- ⟨ id ⟩ (ι′ ≤★)) N) 

data Static {Γ E} : (Γ ⊢ ⟨ E ⟩ A) → Set where

  `_ :
      (x : Γ ∋ A)
      ------------
    → Static (` x)

  ƛ_ : ∀ {F} {N : Γ ▷ A ⊢ ⟨ F ⟩ B}
    → Static N
      ------------
    → Static (ƛ N)

  _·_ : ∀ {L : Γ ⊢ ⟨ E ⟩ (A ⇒ ⟨ E ⟩ B)} {M : Γ ⊢ ⟨ E ⟩ A}
    → Static L
    → Static M
      --------------
    → Static (L · M)

  $_ : ∀ {ι}
    → (k : rep ι)
      -------------------
    → Static ($ k)

  _⦅_⦆_ : ∀ {ι ι′ ι″} {M : Γ ⊢ ⟨ E ⟩ ($ ι)} {N : Γ ⊢ ⟨ E ⟩ ($ ι′)}
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

⌈_⌉ᴳ : Context → Context
⌈ ∅ ⌉ᴳ = ∅
⌈ Γ ▷ A ⌉ᴳ = ⌈ Γ ⌉ᴳ ▷ ★

⌈_⌉ˣ : ∀ {Γ A} → (Γ ∋ A) → (⌈ Γ ⌉ᴳ ∋ ★)
⌈ Z ⌉ˣ          = Z
⌈ S x ⌉ˣ        = S ⌈ x ⌉ˣ

⌈_⌉ : ∀ {M : Γ ⊢ ⟨ E ⟩ A} → Static M → (⌈ Γ ⌉ᴳ ⊢ ⟨ ☆ ⟩ ★)
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
  =  cast (+ ⟨ id ⟩ ℕ≤★) (cast (- ⟨ id ⟩ ℕ≤★) M ⦅ _⊕_ ⦆ cast (- ⟨ id ⟩ ℕ≤★) N)

inc     :  ∅ ⊢ ⟨ ε ⟩ $ℕ ⇒ ⟨ ε ⟩ $ℕ
inc     =  ƛ (` Z ⦅ _+_ ⦆ $ 1)

Inc     :  Static inc
Inc     =  ƛ (` Z ⦅ _+_ ⦆ $ 1)

inc★    :  ∅ ⊢ ⟨ ☆ ⟩ ★
inc★    =  ⌈ Inc ⌉

inc★′   :  ∅ ⊢ ⟨ ☆ ⟩ ★
inc★′   =  cast (+ ⟨ ≤☆ ⟩ ℕ⇒ℕ≤★) inc

inc2—↠3  : inc · ($ 2) —↠ $ 3
inc2—↠3  =
  begin
    (ƛ (` Z ⦅ _+_ ⦆ $ 1)) · $ 2
  —→⟨ ξ □ (β ($ 2)) ⟩
    $ 2 ⦅ _+_ ⦆ $ 1
  —→⟨ ξ □ δ ⟩ $ 3
  ∎

inc★2★—↠3★  : inc★ ·★ ($★ 2) —↠ $★ 3
inc★2★—↠3★  =
  begin
    (ƛ★ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ·★ $ℕ★ 2
  —→⟨ ξ ([ `cast (- ⟨ id ⟩ ★⇒★≤★) [ □ ] ]· $ℕ★ 2) (expand (ƛ _) ★⇒★) ⟩
    (cast (+ ⟨ id ⟩ id) (ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ⇑ ★⇒★) ·★ $ℕ★ 2
  —→⟨ ξ ([ `cast (- ⟨ id ⟩ ★⇒★≤★) [ [ □ ]⇑ ★⇒★ ] ]· $ℕ★ 2) (ident refl (ƛ _)) ⟩
    ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ⇑ ★⇒★) ·★ $ℕ★ 2
  —→⟨ ξ ([ □ ]· $ℕ★ 2) (collapse (ƛ _) ★⇒★) ⟩
    (cast (- ⟨ id ⟩ id) (ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1))) · $ℕ★ 2
  —→⟨ ξ ([ □ ]· $ℕ★ 2) (ident refl (ƛ _)) ⟩
    (ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) · $ℕ★ 2
  —→⟨ ξ □ (β ($ℕ★ 2)) ⟩
    $ℕ★ 2 ⦅ _+_ ⦆ℕ★ $ℕ★ 1
  —→⟨ ξ (`cast (+ ⟨ id ⟩ ℕ≤★) [ [ □ ]⦅ _+_ ⦆ cast (- ⟨ id ⟩ ℕ≤★) ($ℕ★ 1) ]) (collapse ($ 2) $ℕ) ⟩
    cast (+ ⟨ id ⟩ ℕ≤★) (cast (- ⟨ id ⟩ id) ($ 2) ⦅ _+_ ⦆ cast (- ⟨ id ⟩ ℕ≤★) ($ℕ★ 1))
  —→⟨ ξ (`cast (+ ⟨ id ⟩ ℕ≤★) [ [ □ ]⦅ _+_ ⦆ cast (- ⟨ id ⟩ ℕ≤★) ($ℕ★ 1) ]) (ident refl ($ 2)) ⟩
    cast (+ ⟨ id ⟩ ℕ≤★) ($ 2 ⦅ _+_ ⦆ cast (- ⟨ id ⟩ ℕ≤★) ($ℕ★ 1))
  —→⟨ ξ (`cast (+ ⟨ id ⟩ ℕ≤★) [ $ 2 ⦅ _+_ ⦆[ □ ] ]) (collapse ($ 1) $ℕ) ⟩
    cast (+ ⟨ id ⟩ ℕ≤★) ($ 2 ⦅ _+_ ⦆ cast (- ⟨ id ⟩ id) ($ 1))
  —→⟨ ξ (`cast (+ ⟨ id ⟩ ℕ≤★) [ $ 2 ⦅ _+_ ⦆[ □ ] ]) (ident refl ($ 1)) ⟩
    cast (+ ⟨ id ⟩ ℕ≤★) ($ 2 ⦅ _+_ ⦆ $ 1)
  —→⟨ ξ (`cast (+ ⟨ id ⟩ ℕ≤★) [ □ ]) δ ⟩
    cast (+ ⟨ id ⟩ ℕ≤★) ($ 3)
  —→⟨ ξ □ (expand ($ 3) $ℕ) ⟩
    cast (+ ⟨ id ⟩ id) ($ 3) ⇑ $ℕ
  —→⟨ ξ ([ □ ]⇑ $ℕ) (ident refl ($ 3)) ⟩
    $ℕ★ 3
  ∎

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
