```
{-# OPTIONS --show-implicit #-}
module Progress where

open import Utils
open import Type
open import Core

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List.Base using (List; [])
open import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any.Properties as Any
open import Data.String using (String)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Binary.PropositionalEquality
     using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app; subst; inspect)
open import Relation.Binary using (Decidable)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
open import Relation.Nullary.Product using (_×-dec_)
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
handled : ∀ e → Frame Γ P Q → Set
handled e □ = ⊥
handled {Q = ⟨ E ⟩ _} e ([ 𝐸 ]＠⟨ ±p ⟩) = (¬ e ∈¿ E) ⊎ handled e 𝐸
handled e ([ 𝐸 ]＠ ±p) = handled e 𝐸
handled e ([ 𝐸 ]· M) = handled e 𝐸
handled e (M ·[ 𝐸 ]) = handled e 𝐸
handled e ([ 𝐸 ]⦅ f ⦆ M) = handled e 𝐸
handled e (M ⦅ f ⦆[ 𝐸 ]) = handled e 𝐸
handled e ([ 𝐸 ]⇑ g) = handled e 𝐸
handled e (″perform e′∈E [ 𝐸 ] eq) = handled e 𝐸
handled e (′handle H [ 𝐸 ]) = e ∈ H .Hooks ⊎ handled e 𝐸

¬handled-＠⟨⟩ : ∀ {e} {±p : E =>ᵉ F} (𝐸 : Frame Γ P (⟨ E ⟩ A))
  → e ∈¿ F
  → ¬ handled e 𝐸
    -------------------------
  → ¬ handled e ([ 𝐸 ]＠⟨ ±p ⟩)
¬handled-＠⟨⟩ 𝐸 e∈F ¬e//𝐸 (inj₁ ¬e∈F) = ¬e∈F e∈F
¬handled-＠⟨⟩ 𝐸 e∈F ¬e//𝐸 (inj₂ e//𝐸) = ¬e//𝐸 e//𝐸

¬handled-handle : ∀ {e} {H : Γ ⊢ P ➡ Q} (𝐸 : Frame Γ P′ P)
  → ¬ e ∈ Hooks H
  → ¬ handled e 𝐸
    -----------------------------
  → ¬ handled e (′handle H [ 𝐸 ])
¬handled-handle 𝐸 ¬e∈H ¬e//𝐸 (inj₁ e∈H) = ¬e∈H e∈H
¬handled-handle 𝐸 ¬e∈H ¬e//𝐸 (inj₂ e//𝐸) = ¬e//𝐸 e//𝐸

∈¿-++¿ʳ : ∀ {e Eh} → e ∈¿ E → e ∈¿ (Eh ++¿ E)
∈¿-++¿ʳ {Eh = Eh} (¡ e∈E) = ¡ (Any.++⁺ʳ Eh e∈E)
∈¿-++¿ʳ ¿ = ¿

∈¿-++¿⁻ : ∀ {e Eh} → e ∈¿ (Eh ++¿ E) → e ∈ Eh ⊎ e ∈¿ E
∈¿-++¿⁻ {E = ¿} _ = inj₂ ¿
∈¿-++¿⁻ {E = ¡ _} {Eh = Eh} (¡ e∈++) with Any.++⁻ Eh e∈++
... | inj₁ e∈Eh = inj₁ e∈Eh
... | inj₂ e∈E = inj₂ (¡ e∈E)

¬∈-handler : ∀ {e} (H : Γ ⊢ ⟨ E ⟩ A ➡ ⟨ F ⟩ B) → e ∈¿ E → ¬ e ∈ H .Hooks → e ∈¿ F
¬∈-handler H e∈E ¬e∈H rewrite Hooks-handled H with ∈¿-++¿⁻ e∈E
... | inj₁ e∈H = ⊥-elim (¬e∈H e∈H)
... | inj₂ e∈F = e∈F

¬¬-dec : ∀ {P : Set} → Dec P → ¬ ¬ P → P
¬¬-dec (yes p) _ = p
¬¬-dec (no ¬p) ¬¬p = ⊥-elim (¬¬p ¬p)

¬handled-∈ : ∀ {e} (𝐸 : Frame Γ (⟨ E ⟩ A) (⟨ F ⟩ B)) → ¬ handled e 𝐸 → e ∈¿ E → e ∈¿ F
¬handled-∈ □ _ e∈E = e∈E
¬handled-∈ ([ 𝐸 ]· M) ¬e//𝐸 = ¬handled-∈ 𝐸 ¬e//𝐸
¬handled-∈ (v ·[ 𝐸 ]) ¬e//𝐸 = ¬handled-∈ 𝐸 ¬e//𝐸
¬handled-∈ ([ 𝐸 ]⦅ _⊕_ ⦆ N) ¬e//𝐸 = ¬handled-∈ 𝐸 ¬e//𝐸
¬handled-∈ (v ⦅ _⊕_ ⦆[ 𝐸 ]) ¬e//𝐸 = ¬handled-∈ 𝐸 ¬e//𝐸
¬handled-∈ ([ 𝐸 ]⇑ g) ¬e//𝐸 = ¬handled-∈ 𝐸 ¬e//𝐸
¬handled-∈ ([ 𝐸 ]＠⟨ ±p ⟩) ¬e//𝐸 e∈E = ¬¬-dec (_ ∈¿? _) (¬e//𝐸 ∘ inj₁)
¬handled-∈ ([ 𝐸 ]＠ ±p) ¬e//𝐸 = ¬handled-∈ 𝐸 ¬e//𝐸
¬handled-∈ (″perform e∈E [ 𝐸 ] x₁) ¬e//𝐸 = ¬handled-∈ 𝐸 ¬e//𝐸
¬handled-∈ (′handle H [ 𝐸 ]) ¬e//𝐸 e∈E = ¬∈-handler H (¬handled-∈ 𝐸 (¬e//𝐸 ∘ inj₂) e∈E) (¬e//𝐸 ∘ inj₁)
```

```
infix 2 _↦_ _—→_

ƛ-wrap : ∀ (∓s : A′ => A) (±t : P =>ᶜ P′) 
  → (∀ {E} → Γ ⊢ ⟨ E ⟩ (A ⇒ P)) → (∀ {E} → Γ ⊢ ⟨ E ⟩ (A′ ⇒ P′))
ƛ-wrap ∓s ±t M =
  let ⟨ ±te ⟩ ±tv = ±t in
  ƛ (lift M · (` Z ＠ ∓s) ＠⟨ ±te ⟩ ＠ ±tv)

data _↦_ {Γ} : (_ _ : Γ ⊢ P) → Set where

  -- The substitution will put the value under different effects,
  -- the `value` function generalizes the effect of a value.
  β : ∀ {N : Γ ▷ A ⊢ ⟨ E ⟩ B} {W : Γ ⊢ ⟨ E ⟩ A}
    → (w : Value W)
      --------------------
    → (ƛ N) · W ↦ N [ value w ]

  δ : ∀ {ι ι′ ι″} {_⊕_ : rep ι → rep ι′ → rep ι″} {k : rep ι} {k′ : rep ι′}
      --------------------------------------------
    → _⦅_⦆_ {Γ = Γ} {E = E} ($ k) _⊕_ ($ k′) ↦ $ (k ⊕ k′)

  ident : ∀ {V : Γ ⊢ ⟨ E ⟩ A} {±p : A => A}
    → split ±p ≡ id
    → Value V
      --------------
    → (V ＠ ±p) ↦ V

  wrap : {N : Γ ▷ A ⊢ P}
      {∓s : A′ => A} {±t : P =>ᶜ P′} {±p : A ⇒ P => A′ ⇒ P′}
      (let _↦_ = _↦_ {P = ⟨ E ⟩ _} ; infix 2 _↦_)
    → split ±p ≡ ∓s ⇒ ±t
      ----------------------------------------------------
    → (ƛ N) ＠ ±p ↦ ƛ-wrap ∓s ±t (ƛ N)

  expand : ∀{V : Γ ⊢ ⟨ E ⟩ A} {p : A ≤ G}
    → Value V
    → (g : Ground G)
      -------------------------------
    → V ＠ (+ p ⇑ g) ↦ (V ＠ (+ p)) ⇑ g

  collapse : ∀ {V : Γ ⊢ ⟨ E ⟩ G} {p : A ≤ G}
    → Value V
    → (g : Ground G)
      --------------------------------
    → (V ⇑ g) ＠ (- p ⇑ g) ↦ V ＠ (- p)

  collide  : ∀{G H} {V : Γ ⊢ ⟨ E ⟩ G} {p : A ≤ H}
    → Value V
    → (g : Ground G)
    → (h : Ground H)
    → G ≢ H
      -----------------------------
    → (V ⇑ g) ＠ (- p ⇑ h) ↦ blame

  castᵉ-value : {V : Γ ⊢ ⟨ E ⟩ A} {±p : E =>ᵉ F}
    → (v : Value V)
      ----------------------
    → (V ＠⟨ ±p ⟩) ↦ value v

  castᵉ-blame : ∀ {e} {e∈E′ : e ∈¿ E′} {𝐸 : Frame Γ (⟨ E′ ⟩ response e) (⟨ E ⟩ A)} {V} {M}
      {±p : E =>ᵉ F}
    → ¬ e ∈¿ F
    → ¬ handled e 𝐸
    → Value V
    → M ≡ 𝐸 ⟦ perform e∈E′ V ⟧
      ---------------------------
    → M ＠⟨ ±p ⟩ ↦ blame

  handle-value : ∀ {H : Γ ⊢ P ➡ Q} {V}
    → (v : Value V)
      --------------
    → handle H V ↦ (H ._⊢_➡_.on-return [ value v ])

  handle-perform : ∀ {e} {e∈E : e ∈¿ E} {H : Γ ⊢ P ➡ Q} {V 𝐸 e∈Hooks}
    → (v : Value V)
    → ¬ handled e 𝐸                 -- ensures H is the first matching handler
    → (e ∈? Hooks H) ≡ yes e∈Hooks  -- ensures this is the first matching clause within H
                                    -- TODO: a more declarative reformulation?
    → handle H (𝐸 ⟦ perform e∈E V ⟧)
      ↦ All.lookup (on-perform H) e∈Hooks
          [ ƛ (handle (liftʰ (liftʰ H)) (liftᶠ (liftᶠ 𝐸) ⟦ ` Z ⟧)) ]
          [ value v ]
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
infixr 1 _++_
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
_++_ : ∀ {Γ A} {L M N : Γ ⊢ A} → L —↠ M → M —↠ N → L —↠ N
(M ∎) ++ M—↠N                =  M—↠N
(L —→⟨ L—→M ⟩ M—↠N) ++ N—↠P  =  L —→⟨ L—→M ⟩ (M—↠N ++ N—↠P)
```

Alternative notation for sequence concatenation.
```
_—↠⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
  → L —↠ M
  → M —↠ N
    ---------
  → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N  =  L—↠M ++ M—↠N
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
    → (e∈E : e ∈¿ E)
    → Value V
    → ¬ handled e 𝐸
      ------------------
    → Progress (𝐸 ⟦ perform e∈E V ⟧)

progress± : ∀ {V : ∅ ⊢ ⟨ E ⟩ A}
  → (v : Value V)
  → (±p : A => B)
    --------------------
  → ∃[ M ](V ＠ ±p ↦ M)
progress± v ±p with split ±p in e
progress± v     _ | id                   =  _ , ident e v
progress± (ƛ _) _ | _ ⇒ _                =  _ , wrap e
progress± v       (+ _ ⇑ g) | other      =  _ , expand v g
progress± (v ⇑ g) (- _ ⇑ h) | other
    with ground g ≡? ground h
... | yes refl rewrite uniqueG g h       =  _ , collapse v h
... | no  G≢H                            =  _ , collide v g h G≢H

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
progress (M ＠⟨⟩ ±p) with progress M
progress (M ＠⟨⟩ ±p)  | blame 𝐸           =  blame ([ 𝐸 ]＠⟨⟩ ±p)
progress (M ＠⟨⟩ ±p)  | step (ξ 𝐸 M↦M′)   =  step (ξ ([ 𝐸 ]＠⟨⟩ ±p) M↦M′)
progress (M ＠   ±p)  | done v with progress± v ±p
... | _ , V⟨±p⟩↦N                        = step (ξ □ V⟨±p⟩↦N)
progress (M ＠⟨ ±p ⟩) | done v           = step (ξ □ (castᵉ-value v))
progress (M ＠   ±p)  | performing 𝐸 e∈E v ¬e//𝐸
                                         = performing ([ 𝐸 ]＠ ±p) e∈E v ¬e//𝐸
progress (M ＠⟨⟩ ⟨_⟩- {F = F} ±p) | performing {e = e} 𝐸 e∈E v ¬e//𝐸
    with e ∈¿? F
... | yes e∈F = performing ([ 𝐸 ]＠⟨ ±p ⟩) e∈E v (¬handled-＠⟨⟩ {±p = ±p} 𝐸 e∈F ¬e//𝐸)
... | no  ¬∈  = step (ξ □ (castᵉ-blame ¬∈ ¬e//𝐸 v refl))
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
    → (e∈E : e ∈¿ E)
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

pattern  ƛ★_ N          =  (ƛ N) ＠ (+ ★⇒★≤★)
pattern  _·★_ L M       =  (L ＠ (- ★⇒★≤★)) · M
pattern  $★_ {ι = ι} k  =  $ k ⇑ $ ι
pattern  _⦅_⦆★_ {ι = ι} {ι′} {ι″} M _⊕_ N
  =  ((M ＠ (- ι ≤★)) ⦅ _⊕_ ⦆ (N ＠ (- ι′ ≤★))) ＠ (+ ι″ ≤★)

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

⌈_⌉ : ∀ {M : Γ ⊢ ⟨ E ⟩ A} → Static M → (⌈ Γ ⌉ᴳ ⊢ ⟨ ¿ ⟩ ★)
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
ℕ⇒ℕ≤★' =  ℕ≤★ ⇒ ⟨ E≤¿ ⟩ ℕ≤★ ⇑ ★⇒★

pattern ε≤¿ = ¡≤¿ {E = []}

pattern  ℕ⇒ℕ≤★   =  ℕ≤★ ⇒ ⟨ ¡≤¿ ⟩ ℕ≤★ ⇑ ★⇒★

infix  6 _⦅_⦆ℕ★_
infix  8 $ℕ★_
infix  8 $𝔹★_

pattern  $ℕ★_ k          =  $ k ⇑ $ℕ
pattern  $𝔹★_ k          =  $ k ⇑ $𝔹
pattern  _⦅_⦆ℕ★_ M _⊕_ N
  =  ((M ＠ (- ℕ≤★)) ⦅ _⊕_ ⦆ (N ＠ (- ℕ≤★))) ＠ (+ ℕ≤★)

inc     :  ∅ ⊢ ⟨ ε ⟩ $ℕ ⇒ ⟨ ε ⟩ $ℕ
inc     =  ƛ (` Z ⦅ _+_ ⦆ $ 1)

Inc     :  Static inc
Inc     =  ƛ (` Z ⦅ _+_ ⦆ $ 1)

inc★    :  ∅ ⊢ ⟨ ¿ ⟩ ★
inc★    =  ⌈ Inc ⌉

inc★′   :  ∅ ⊢ ⟨ ¿ ⟩ ★
inc★′   =  inc ＠⟨ + E≤¿ ⟩ ＠ (+ ℕ⇒ℕ≤★)

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
  —→⟨ ξ ([ [ □ ]＠ (- ★⇒★≤★) ]· $ℕ★ 2) (expand (ƛ _) ★⇒★) ⟩
    (((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ＠ (+ id)) ⇑ ★⇒★) ·★ $ℕ★ 2
  —→⟨ ξ ([ [ [ □ ]⇑ ★⇒★ ]＠ (- ★⇒★≤★) ]· $ℕ★ 2) (ident refl (ƛ _)) ⟩
    ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ⇑ ★⇒★) ·★ $ℕ★ 2
  —→⟨ ξ ([ □ ]· $ℕ★ 2) (collapse (ƛ _) ★⇒★) ⟩
    ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ＠ (- id)) · $ℕ★ 2
  —→⟨ ξ ([ □ ]· $ℕ★ 2) (ident refl (ƛ _)) ⟩
    (ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) · $ℕ★ 2
  —→⟨ ξ □ (β ($ℕ★ 2)) ⟩
    $ℕ★ 2 ⦅ _+_ ⦆ℕ★ $ℕ★ 1
  —→⟨ ξ ([ [ □ ]⦅ _+_ ⦆ ($ℕ★ 1 ＠ (- ℕ≤★)) ]＠ (+ ℕ≤★)) (collapse ($ 2) $ℕ) ⟩
    ($ 2 ＠ (- id)) ⦅ _+_ ⦆ ($ℕ★ 1 ＠ (- ℕ≤★)) ＠ (+ ℕ≤★)
  —→⟨ ξ ([ [ □ ]⦅ _+_ ⦆ ($ℕ★ 1 ＠ (- ℕ≤★)) ]＠ (+ ℕ≤★)) (ident refl ($ 2)) ⟩
    $ 2 ⦅ _+_ ⦆ ($ℕ★ 1 ＠ (- ℕ≤★)) ＠ (+ ℕ≤★)
  —→⟨ ξ ([ $ 2 ⦅ _+_ ⦆[ □ ] ]＠ (+ ℕ≤★)) (collapse ($ 1) $ℕ) ⟩
    $ 2 ⦅ _+_ ⦆ ($ 1 ＠ (- id)) ＠ (+ ℕ≤★)
  —→⟨ ξ ([ $ 2 ⦅ _+_ ⦆[ □ ] ]＠ (+ ℕ≤★)) (ident refl ($ 1)) ⟩
    $ 2 ⦅ _+_ ⦆ $ 1 ＠ (+ ℕ≤★)
  —→⟨ ξ ([ □ ]＠ (+ ℕ≤★)) δ ⟩
    ($ 3 ＠ (+ ℕ≤★))
  —→⟨ ξ □ (expand ($ 3) $ℕ) ⟩
    ($ 3 ＠ (+ id)) ⇑ $ℕ
  —→⟨ ξ ([ □ ]⇑ $ℕ) (ident refl ($ 3)) ⟩
    $ℕ★ 3
  ∎

inc★′2★—↠3★  : inc★′ ·★ ($★ 2) —↠ $★ 3
inc★′2★—↠3★  =
  begin
    ((ƛ (` Z ⦅ _+_ ⦆ $ 1)) ＠⟨ + E≤¿ ⟩ ＠ (+ ℕ⇒ℕ≤★)) ·★ $ℕ★ 2
  —→⟨ ξ ([ [ [ □ ]＠ (+ ℕ⇒ℕ≤★) ]＠ (- ★⇒★≤★) ]· $ℕ★ 2) (castᵉ-value (ƛ _)) ⟩
    ((ƛ (` Z ⦅ _+_ ⦆ $ 1)) ＠ (+ ℕ⇒ℕ≤★)) ·★ $ℕ★ 2
  —→⟨ ξ ([ [ □ ]＠ (- ★⇒★≤★) ]· $ℕ★ 2) (expand (ƛ _) ★⇒★) ⟩
    ((ƛ (` Z ⦅ _+_ ⦆ $ 1)) ＠ (+ ℕ≤★ ⇒ ⟨ E≤¿ ⟩ ℕ≤★) ⇑ ★⇒★) ·★ $ℕ★ 2
  —→⟨ ξ ([ [ [ □ ]⇑ ★⇒★ ]＠ (- ★⇒★≤★) ]· $ℕ★ 2) (wrap refl) ⟩
    let f = ƛ ((ƛ (` Z ⦅ _+_ ⦆ $ 1)) · (` Z ＠ (- ℕ≤★)) ＠⟨ + E≤¿ ⟩ ＠ (+ ℕ≤★)) in
    (f ⇑ ★⇒★) ·★ $ℕ★ 2
  —→⟨ ξ ([ □ ]· $ℕ★ 2) (collapse (ƛ _) ★⇒★) ⟩
    (f ＠ (- id)) · $ℕ★ 2
  —→⟨ ξ ([ □ ]· $ℕ★ 2) (ident refl (ƛ _)) ⟩
    f · $ℕ★ 2
  —→⟨ ξ □ (β ($ℕ★ 2)) ⟩
    (ƛ (` Z ⦅ _+_ ⦆ $ 1)) · ($ℕ★ 2 ＠ (- ℕ≤★)) ＠⟨ + E≤¿ ⟩ ＠ (+ ℕ≤★)
  —→⟨ ξ ([ [ (ƛ (` Z ⦅ _+_ ⦆ $ 1)) ·[ □ ] ]＠⟨ + E≤¿ ⟩ ]＠ (+ ℕ≤★)) (collapse ($ 2) $ℕ) ⟩
    (ƛ (` Z ⦅ _+_ ⦆ $ 1)) · ($ 2 ＠ (- id)) ＠⟨ + E≤¿ ⟩ ＠ (+ ℕ≤★)
  —→⟨ ξ ([ [ (ƛ (` Z ⦅ _+_ ⦆ $ 1)) ·[ □ ] ]＠⟨ + E≤¿ ⟩ ]＠ (+ ℕ≤★)) (ident refl ($ 2)) ⟩
    (ƛ (` Z ⦅ _+_ ⦆ $ 1)) · $ 2 ＠⟨ + E≤¿ ⟩ ＠ (+ ℕ≤★)
  —→⟨ ξ ([ [ □ ]＠⟨ + E≤¿ ⟩ ]＠ (+ ℕ≤★)) (β ($ 2)) ⟩
    $ 2 ⦅ _+_ ⦆ $ 1 ＠⟨ + E≤¿ ⟩ ＠ (+ ℕ≤★)
  —→⟨ ξ ([ [ □ ]＠⟨ + E≤¿ ⟩ ]＠ (+ ℕ≤★)) δ ⟩
    $ 3 ＠⟨ + E≤¿ ⟩ ＠ (+ ℕ≤★)
  —→⟨ ξ ([ □ ]＠ (+ ℕ≤★)) (castᵉ-value ($ 3)) ⟩
    $ 3 ＠ (+ ℕ≤★)
  —→⟨ ξ □ (expand ($ 3) $ℕ) ⟩
    $ 3 ＠ (+ id) ⇑ $ℕ
  —→⟨ ξ ([ □ ]⇑ $ℕ) (ident refl ($ 3)) ⟩
    $ℕ★ 3
  ∎

inc★true★—↠blame : inc★ ·★ ($★ true) —↠
  ([ [ □ ]⦅ _+_ ⦆ ($ℕ★ 1 ＠ (- ℕ≤★)) ]＠ (+ ℕ≤★)) ⟦ blame ⟧
inc★true★—↠blame =
  begin
    (ƛ★ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ·★ $𝔹★ true
  —→⟨ ξ ([ [ □ ]＠ (- ★⇒★≤★) ]· $𝔹★ true) (expand (ƛ _) ★⇒★) ⟩
    ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ＠ (+ id) ⇑ ★⇒★) ·★ $𝔹★ true
  —→⟨ ξ ([ [ [ □ ]⇑ ★⇒★ ]＠ (- ★⇒★≤★) ]· $𝔹★ true) (ident refl (ƛ _)) ⟩
    ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ⇑ ★⇒★) ·★ $𝔹★ true
  —→⟨ ξ ([ □ ]· $𝔹★ true) (collapse (ƛ _) ★⇒★) ⟩
    ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ＠ (- id)) · $𝔹★ true
  —→⟨ ξ ([ □ ]· $𝔹★ true) (ident refl (ƛ _)) ⟩
    (ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) · $𝔹★ true
  —→⟨ ξ □ (β ($𝔹★ true)) ⟩
    $𝔹★ true ⦅ _+_ ⦆ℕ★ $ℕ★ 1
  —→⟨ ξ ([ [ □ ]⦅ _+_ ⦆ ($ℕ★ 1 ＠ (- ℕ≤★)) ]＠ (+ ℕ≤★)) (collide ($ true) $𝔹 $ℕ (λ())) ⟩
    blame ⦅ _+_ ⦆ ($ℕ★ 1 ＠ (- ℕ≤★)) ＠ (+ ℕ≤★)
  ∎
```
