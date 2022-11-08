# Operational Semantics

```
{-# OPTIONS --show-implicit #-}
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

data Frame (Γ : Context) (C : Typeᶜ) : Typeᶜ → Set where

  □ : Frame Γ C C

  [_]·_ : ∀ {E A B}
    →  (𝐸 : Frame Γ C (⟨ E ⟩ (A ⇒ ⟨ E ⟩ B)))
    →  (M : Γ ⊢ ⟨ E ⟩ A)
       ---------------
    →  Frame Γ C (⟨ E ⟩ B)

  _·[_] : ∀ {E A B}{V : Γ ⊢ ⟨ E ⟩ (A ⇒ ⟨ E ⟩ B)}
    →  (v : Value V)
    →  (𝐸 : Frame Γ C (⟨ E ⟩ A))
       ----------------
    →  Frame Γ C (⟨ E ⟩ B)

  [_]⦅_⦆_ : ∀ {E ι ι′ ι″}
    →  (𝐸 : Frame Γ C (⟨ E ⟩ ($ ι)))
    →  (_⊕_ : rep ι → rep ι′ → rep ι″)
    →  (N : Γ ⊢ ⟨ E ⟩ ($ ι′))
       ------------------
    →  Frame Γ C (⟨ E ⟩ ($ ι″))

  _⦅_⦆[_] : ∀ {E ι ι′ ι″}{V : Γ ⊢ ⟨ E ⟩ $ ι}
    →  (v : Value V)
    →  (_⊕_ : rep ι → rep ι′ → rep ι″)
    →  (𝐸 : Frame Γ C (⟨ E ⟩ ($ ι′)))
       -------------------
    →  Frame Γ C (⟨ E ⟩ ($ ι″))

  [_]⇑_ : ∀ {E G}
    →  (𝐸 : Frame Γ C (⟨ E ⟩ G))
    →  (g : Ground G)
       --------------
    →  Frame Γ C (⟨ E ⟩ ★)

  `cast_[_] : ∀ {P Q}
    →  (±p : P =>ᶜ Q)
    →  (𝐸 : Frame Γ C P)
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

pattern ′perform_[_] e 𝐸 = ″perform e [ 𝐸 ] refl
```

The plug function inserts an expression into the hole of a frame.
```
_⟦_⟧ : ∀{Γ A B} → Frame Γ A B → Γ ⊢ A → Γ ⊢ B
□ ⟦ M ⟧                 =  M
([ 𝐸 ]· M) ⟦ L ⟧        =  𝐸 ⟦ L ⟧ · M
(v ·[ 𝐸 ]) ⟦ M ⟧        =  value v · 𝐸 ⟦ M ⟧
([ 𝐸 ]⦅ _⊕_ ⦆ N) ⟦ M ⟧  =  𝐸 ⟦ M ⟧ ⦅ _⊕_ ⦆ N
(v ⦅ _⊕_ ⦆[ 𝐸 ]) ⟦ N ⟧  =  value v ⦅ _⊕_ ⦆ 𝐸 ⟦ N ⟧
([ 𝐸 ]⇑ g) ⟦ M ⟧        =  𝐸 ⟦ M ⟧ ⇑ g
(`cast ±p [ 𝐸 ]) ⟦ M ⟧  =  cast ±p (𝐸 ⟦ M ⟧)
(″perform e∈E [ 𝐸 ] eq) ⟦ M ⟧ = perform- e∈E eq (𝐸 ⟦ M ⟧)
(′handle H [ 𝐸 ]) ⟦ M ⟧ = handle H (𝐸 ⟦ M ⟧)
```

Composition of two frames
```
_∘∘_ : ∀{Γ A B C} → Frame Γ B C → Frame Γ A B → Frame Γ A C
□ ∘∘ 𝐹                 =  𝐹
([ 𝐸 ]· M) ∘∘ 𝐹        =  [ 𝐸 ∘∘ 𝐹 ]· M
(v ·[ 𝐸 ]) ∘∘ 𝐹        =  v ·[ 𝐸 ∘∘ 𝐹 ]
([ 𝐸 ]⦅ _⊕_ ⦆ N) ∘∘ 𝐹  =  [ 𝐸 ∘∘ 𝐹 ]⦅ _⊕_ ⦆ N
(v ⦅ _⊕_ ⦆[ 𝐸 ]) ∘∘ 𝐹  =  v ⦅ _⊕_ ⦆[ 𝐸 ∘∘ 𝐹 ]
([ 𝐸 ]⇑ g) ∘∘ 𝐹        =  [ 𝐸 ∘∘ 𝐹 ]⇑ g
(`cast ±p [ 𝐸 ]) ∘∘ 𝐹     =  `cast ±p [ 𝐸 ∘∘ 𝐹 ]
(″perform e∈E [ 𝐸 ] eq) ∘∘ 𝐹 = ″perform e∈E [ 𝐸 ∘∘ 𝐹 ] eq
(′handle H [ 𝐸 ]) ∘∘ 𝐹  =  ′handle H [ 𝐸 ∘∘ 𝐹 ]
```

Composition and plugging
```
∘∘-lemma : ∀ {Γ A B C}
  → (𝐸 : Frame Γ B C)
  → (𝐹 : Frame Γ A B)
  → (M : Γ ⊢ A)
    -----------------------------
  → 𝐸 ⟦ 𝐹 ⟦ M ⟧ ⟧ ≡ (𝐸 ∘∘ 𝐹) ⟦ M ⟧
∘∘-lemma □ 𝐹 M                                         =  refl
∘∘-lemma ([ 𝐸 ]· M₁) 𝐹 M       rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
∘∘-lemma (v ·[ 𝐸 ]) 𝐹 M        rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
∘∘-lemma ([ 𝐸 ]⦅ _⊕_ ⦆ N) 𝐹 M  rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
∘∘-lemma (v ⦅ _⊕_ ⦆[ 𝐸 ]) 𝐹 M  rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
∘∘-lemma ([ 𝐸 ]⇑ g) 𝐹 M        rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
∘∘-lemma (`cast ±p [ 𝐸 ]) 𝐹 M  rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
∘∘-lemma (″perform e∈E [ 𝐸 ] eq) 𝐹 M rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
∘∘-lemma (′handle H [ 𝐸 ]) 𝐹 M rewrite ∘∘-lemma 𝐸 𝐹 M  =  refl
```

```
renᶠ : ∀ {Γ Δ P Q} → Γ →ᴿ Δ → Frame Γ P Q → Frame Δ P Q
renᶠ ρ □ = □
renᶠ ρ ([ 𝐸 ]· M) = [ renᶠ ρ 𝐸 ]· ren ρ M
renᶠ ρ (v ·[ 𝐸 ]) = ren-val ρ v ·[ renᶠ ρ 𝐸 ]
renᶠ ρ ([ 𝐸 ]⦅ f ⦆ M) = [ renᶠ ρ 𝐸 ]⦅ f ⦆ ren ρ M
renᶠ ρ (v ⦅ f ⦆[ 𝐸 ]) = ren-val ρ v ⦅ f ⦆[ renᶠ ρ 𝐸 ]
renᶠ ρ ([ 𝐸 ]⇑ g) = [ renᶠ ρ 𝐸 ]⇑ g
renᶠ ρ (`cast ±p [ 𝐸 ]) = `cast ±p [ renᶠ ρ 𝐸 ]
renᶠ ρ (″perform e∈E [ 𝐸 ] eq) = ″perform e∈E [ renᶠ ρ 𝐸 ] eq
renᶠ ρ (′handle H [ 𝐸 ]) = ′handle (renʰ ρ H) [ renᶠ ρ 𝐸 ]

liftᶠ : ∀ {Γ P Q A} → Frame Γ P Q → Frame (Γ ▷ A) P Q
liftᶠ = renᶠ S_

liftʰ : ∀ {Γ P Q A} → Γ ⊢ P ➡ Q → Γ ▷ A ⊢ P ➡ Q
liftʰ = renʰ S_
```

```
private
  variable
    A A′ B G : Type
    P P′ Q Q′ : Typeᶜ
    E E′ F : Effs
    Γ : Context
```

## Reduction

```
cast-effect : {P Q : Typeᶜ} → P =>ᶜ Q → Effs
cast-effect {Q = ⟨ E ⟩ B} _ = E

handled : ∀ e → Frame Γ P Q → Set
handled e □ = ⊥
handled {Q = ⟨ E ⟩ _} e (`cast ±p [ 𝐸 ]) = (¬ e ∈☆ cast-effect ±p) ⊎ handled e 𝐸
handled e ([ 𝐸 ]· M) = handled e 𝐸
handled e (M ·[ 𝐸 ]) = handled e 𝐸
handled e ([ 𝐸 ]⦅ f ⦆ M) = handled e 𝐸
handled e (M ⦅ f ⦆[ 𝐸 ]) = handled e 𝐸
handled e ([ 𝐸 ]⇑ g) = handled e 𝐸
handled e (″perform e′∈E [ 𝐸 ] eq) = handled e 𝐸
handled e (′handle H [ 𝐸 ]) = e ∈ H .Hooks ⊎ handled e 𝐸

¬handled-cast : ∀ {e} {±p : (⟨ E ⟩ A) =>ᶜ (⟨ F ⟩ B)} (𝐸 : Frame Γ P (⟨ E ⟩ A))
  → e ∈☆ F
  → ¬ handled e 𝐸
    -------------------------
  → ¬ handled e (`cast ±p [ 𝐸 ])
¬handled-cast 𝐸 e∈F ¬e//𝐸 (inj₁ ¬e∈F) = ¬e∈F e∈F
¬handled-cast 𝐸 e∈F ¬e//𝐸 (inj₂ e//𝐸) = ¬e//𝐸 e//𝐸

¬handled-handle : ∀ {e} {H : Γ ⊢ P ➡ Q} (𝐸 : Frame Γ P′ P)
  → ¬ e ∈ Hooks H
  → ¬ handled e 𝐸
    -----------------------------
  → ¬ handled e (′handle H [ 𝐸 ])
¬handled-handle 𝐸 ¬e∈H ¬e//𝐸 (inj₁ e∈H) = ¬e∈H e∈H
¬handled-handle 𝐸 ¬e∈H ¬e//𝐸 (inj₂ e//𝐸) = ¬e//𝐸 e//𝐸

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

¬handled-∈ : ∀ {e} (𝐸 : Frame Γ (⟨ E ⟩ A) (⟨ F ⟩ B)) → ¬ handled e 𝐸 → e ∈☆ E → e ∈☆ F
¬handled-∈ □ _ e∈E = e∈E
¬handled-∈ ([ 𝐸 ]· M) ¬e//𝐸 = ¬handled-∈ 𝐸 ¬e//𝐸
¬handled-∈ (v ·[ 𝐸 ]) ¬e//𝐸 = ¬handled-∈ 𝐸 ¬e//𝐸
¬handled-∈ ([ 𝐸 ]⦅ _⊕_ ⦆ N) ¬e//𝐸 = ¬handled-∈ 𝐸 ¬e//𝐸
¬handled-∈ (v ⦅ _⊕_ ⦆[ 𝐸 ]) ¬e//𝐸 = ¬handled-∈ 𝐸 ¬e//𝐸
¬handled-∈ ([ 𝐸 ]⇑ g) ¬e//𝐸 = ¬handled-∈ 𝐸 ¬e//𝐸
¬handled-∈ (`cast ±p [ 𝐸 ]) ¬e//𝐸 e∈E = ¬¬-dec (_ ∈☆? _) (¬e//𝐸 ∘ inj₁)
¬handled-∈ (″perform e∈E [ 𝐸 ] x₁) ¬e//𝐸 = ¬handled-∈ 𝐸 ¬e//𝐸
¬handled-∈ (′handle H [ 𝐸 ]) ¬e//𝐸 e∈E = ¬∈-handler H (¬handled-∈ 𝐸 (¬e//𝐸 ∘ inj₂) e∈E) (¬e//𝐸 ∘ inj₁)
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

  castᵉ-blame : ∀ {e} {e∈E′ : e ∈☆ E′} {𝐸 : Frame Γ (⟨ E′ ⟩ response e) (⟨ E ⟩ A)} {V} {M}
      {±p : ⟨ E ⟩ A =>ᶜ ⟨ F ⟩ B}
    → ¬ e ∈☆ F
    → ¬ handled e 𝐸
    → Value V
    → M ≡ 𝐸 ⟦ perform e∈E′ V ⟧
      ---------------------------
    → cast ±p M ↦ blame

  handle-value : ∀ {H : Γ ⊢ P ➡ Q} {V}
    → (v : Value V)
      --------------
    → handle H V ↦ (H ._⊢_➡_.on-return [ gvalue v ])

  handle-perform : ∀ {e} {e∈E : e ∈☆ E} {H : Γ ⊢ P ➡ Q} {V 𝐸 e∈Hooks}
    → (v : Value V)
    → ¬ handled e 𝐸                 -- ensures H is the first matching handler
    → (e ∈? Hooks H) ≡ yes e∈Hooks  -- ensures this is the first matching clause within H
                                    -- TODO: a more declarative reformulation?
    → handle H (𝐸 ⟦ perform e∈E V ⟧)
      ↦ All.lookup (on-perform H) e∈Hooks
          [ ƛ (handle (liftʰ (liftʰ H)) (liftᶠ (liftᶠ 𝐸) ⟦ ` Z ⟧)) ]
          [ gvalue v ]
    -- TODO: explain the order of these substitutions and why the 2 lifts

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξξ : ∀ {Γ A B} {M N : Γ ⊢ A} {M′ N′ : Γ ⊢ B}
    → ( 𝐸 : Frame Γ A B)
    → M′ ≡ 𝐸 ⟦ M ⟧
    → N′ ≡ 𝐸 ⟦ N ⟧
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
   nope (ξ □ (castᵉ-blame ¬∈ e//𝐸 v′ eq)) ()
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
unframe-blame : ∀ {M} (𝐸 : Frame Γ P Q) → blame ≡ 𝐸 ⟦ M ⟧ → blame ≡ M
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

  performing : ∀ {e} {V} 𝐸
    → (e∈E : e ∈☆ E)
    → Value V
    → ¬ handled e 𝐸
      ------------------
    → Progress (𝐸 ⟦ perform e∈E V ⟧)

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
... | blame 𝐸                            =  blame ([ 𝐸 ]· M)
... | step (ξ 𝐸 L↦L′)                    =  step (ξ ([ 𝐸 ]· M) L↦L′)
... | performing 𝐸 e∈E v ¬e//𝐸           =  performing ([ 𝐸 ]· M) e∈E v ¬e//𝐸
... | done (ƛ N) with progress M
...     | blame 𝐸                        =  blame ((ƛ N) ·[ 𝐸 ])
...     | step (ξ 𝐸 M↦M′)                =  step (ξ ((ƛ N) ·[ 𝐸 ]) M↦M′)
...     | performing 𝐸 e∈E v ¬e//𝐸       =  performing ((ƛ N) ·[ 𝐸 ]) e∈E v ¬e//𝐸
...     | done w                         =  step (ξ □ (β w))
progress ($ k)                           =  done ($ k)
progress (L ⦅ _⊕_ ⦆ M) with progress L
... | blame 𝐸                            =  blame ([ 𝐸 ]⦅ _⊕_ ⦆ M)
... | step (ξ 𝐸 L↦L′)                    =  step (ξ ([ 𝐸 ]⦅ _⊕_ ⦆ M) L↦L′)
... | performing 𝐸 e∈E v ¬e//𝐸           =  performing ([ 𝐸 ]⦅ _⊕_ ⦆ M) e∈E v ¬e//𝐸
... | done ($ k) with progress M
...     | blame 𝐸                        =  blame (($ k) ⦅ _⊕_ ⦆[ 𝐸 ])
...     | step (ξ 𝐸 M↦M′)                =  step (ξ (($ k) ⦅ _⊕_ ⦆[ 𝐸 ]) M↦M′)
...     | performing 𝐸 e∈E v ¬e//𝐸       =  performing (($ k) ⦅ _⊕_ ⦆[ 𝐸 ]) e∈E v ¬e//𝐸
...     | done ($ k′)                    =  step (ξ □ δ)
progress (M ⇑ g) with progress M
... | blame 𝐸                            =  blame ([ 𝐸 ]⇑ g)
... | step (ξ 𝐸 M↦M′)                    =  step (ξ ([ 𝐸 ]⇑ g) M↦M′)
... | performing 𝐸 e∈E v ¬e//𝐸            =  performing ([ 𝐸 ]⇑ g) e∈E v ¬e//𝐸
... | done v                             =  done (v ⇑ g)
progress (cast ±p M) with progress M
... | blame 𝐸           =  blame (`cast ±p [ 𝐸 ])
... | step (ξ 𝐸 M↦M′)   =  step (ξ (`cast ±p [ 𝐸 ]) M↦M′)
progress (cast {Q = ⟨ F ⟩ _} ±p M)
    | performing {e = e} 𝐸 e∈E v ¬e//𝐸
        with e ∈☆? F
...     | yes e∈F = performing (`cast ±p [ 𝐸 ]) e∈E v (¬handled-cast {±p = ±p} 𝐸 e∈F ¬e//𝐸)
...     | no  ¬∈  = step (ξ □ (castᵉ-blame ¬∈ ¬e//𝐸 v refl))
progress (cast ±p M) 
    | done v
        with progress± v ±p
...     | _ , V⟨±p⟩↦N                        = step (ξ □ V⟨±p⟩↦N)
progress blame                           =  blame □
progress (perform- e∈E eq M) with progress M
... | blame 𝐸                            = blame (″perform e∈E [ 𝐸 ] eq)
... | step (ξ 𝐸 M↦M′)                    = step (ξ (″perform e∈E [ 𝐸 ] eq) M↦M′)
... | performing 𝐸 e′∈E′ v ¬e′//𝐸        = performing (″perform e∈E [ 𝐸 ] eq) e′∈E′ v ¬e′//𝐸
... | done v with eq
...   | refl = performing □ e∈E v (λ())
progress (handle H M) with progress M
... | blame 𝐸 = blame (′handle H [ 𝐸 ])
... | step (ξ 𝐸 M↦M′) = step (ξ (′handle H [ 𝐸 ]) M↦M′)
... | done v = step (ξ □ (handle-value v))
... | performing {e = e} 𝐸 e∈E v ¬e//𝐸 with e ∈? Hooks H in eq
...   | yes e∈H = step (ξ □ (handle-perform v ¬e//𝐸 eq))
...   | no ¬e∈H = performing (′handle H [ 𝐸 ]) e∈E v (¬handled-handle {H = H} 𝐸 ¬e∈H ¬e//𝐸)
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

  performing : ∀ {e V 𝐸}
    → (e∈E : e ∈☆ E)
    → Value V
    → (e//𝐸 : ¬ handled e 𝐸)
      ------------------------------
    → Finished (𝐸 ⟦ perform e∈E V ⟧)

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
... | performing 𝐸 e∈E v ¬e//𝐸 =  steps (L ∎) (performing e∈E v ¬e//𝐸)
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

## Examples

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
