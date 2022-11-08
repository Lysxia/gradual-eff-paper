Simple Blame Calculus with proof relevant casts.
Uses polarity to unify upcasts and downcasts.
Uses nested evaluation contexts.

Siek, Thiemann, and Wadler

```
module Sim where

open import Utils
open import Type
open import Core
open import Progress
open import Prec
open import SimAux
```

## Term precision is a simulation (Gradual Guarantee)
```
sim : ∀ {Γ Γ′ A A′ E E′ M M′ N} {Γ≤ : Γ ≤ᴳ Γ′} {p : A ≤ A′} {E≤ : E ≤ᵉ E′}
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ p
  → M —→ N
    -----------------------------------------
  → ∃[ N′ ]((M′ —↠ N′) × (Γ≤ ⊢ N ≤ᴹ N′ ⦂ ⟨ E≤ ⟩ p))
sim (`≤` x≤x′) M—→N
    =  ⊥-elim (variable-irreducible M—→N)
sim (ƛ≤ƛ ƛN≤ƛN′) M—→N
    =  ⊥-elim (value-irreducible (ƛ _) M—→N)
sim (·≤· L≤L′ M≤M′) (ξ ([ E ]· _) L↦N)
    with sim L≤L′ (ξ E L↦N)
... |  N′ , L′—↠N′ , N≤N′
    =  N′ · _ , ξ* ([ □ ]· _) L′—↠N′ , ·≤· N≤N′ M≤M′
sim (·≤· V≤L′ M≤M′) (ξ (v ·[ E ]) M↦N)
    with catchup v V≤L′
... |  V′ , v′ , L′—↠V′ , V≤V′
    with sim M≤M′ (ξ E M↦N)
... |  N′ , M′—↠N′ , N≤N′
    =  V′ · N′ , (ξ* ([ □ ]· _) L′—↠V′ ++↠ ξ* (v′ ·[ □ ]) M′—↠N′) , ·≤· V≤V′ N≤N′
sim (·≤· ƛN≤L′ W≤M′) (ξ □ (β w))
    with catchup (ƛ _) ƛN≤L′
... |  ƛ N′ , v′ , L′—↠ƛN′ , ƛN≤ƛN′
    with catchup w W≤M′
... |  W′ , w′ , M′—↠W′ , W≤W′
    with simβ w w′ ƛN≤ƛN′ W≤W′
... |  M′ , ƛN′·W′—↠M′ , N[V]≤M′
    =  M′ , (ξ* ([ □ ]· _) L′—↠ƛN′ ++↠ ξ* (v′ ·[ □ ]) M′—↠W′ ++↠ ƛN′·W′—↠M′) , N[V]≤M′
sim ($≤$ k) M—→N
    =  ⊥-elim (value-irreducible ($ _) M—→N)
sim (⦅⦆≤⦅⦆ _⊕_ L≤L′ M≤M′) (ξ ([ E ]⦅ ._⊕_ ⦆ _) L↦N)
    with sim L≤L′ (ξ E L↦N)
... |  N′ , L′—↠N′ , N≤N′
    =  N′ ⦅ _⊕_ ⦆ _ , ξ* ([ □ ]⦅ _⊕_ ⦆ _) L′—↠N′ , ⦅⦆≤⦅⦆ _⊕_ N≤N′ M≤M′
sim (⦅⦆≤⦅⦆ _⊕_ V≤L′ M≤M′) (ξ (v ⦅ ._⊕_ ⦆[ E ]) M↦N)
    with catchup v V≤L′
... |  V′ , v′ , L′—↠V′ , V≤V′
    with sim M≤M′ (ξ E M↦N)
... |  N′ , M′—↠N′ , N≤N′
    =  V′ ⦅ _⊕_ ⦆ N′ , (ξ* ([ □ ]⦅ _⊕_ ⦆ _) L′—↠V′ ++↠ ξ* (v′ ⦅ _⊕_ ⦆[ □ ]) M′—↠N′) , ⦅⦆≤⦅⦆ _⊕_ V≤V′ N≤N′
sim (⦅⦆≤⦅⦆ _⊕_ V≤L′ W≤M′) (ξ □ δ)
    with catchup ($ _) V≤L′
... |  $ k , $ .k , L′—↠V′ , ($≤$ .k)
    with catchup ($ _) W≤M′
... |  $ k′ , $ .k′ , M′—↠W′ , ($≤$ .k′)
    =  $ (k ⊕ k′) , (ξ* ([ □ ]⦅ _⊕_ ⦆ _) L′—↠V′ ++↠ ξ* ($ k ⦅ _⊕_ ⦆[ □ ]) M′—↠W′ ++↠ unit δ) , $≤$ (k ⊕ k′)
sim (⇑≤⇑ g M≤M′) (ξ □ M↦N)
    =  ⊥-elim (box-irreducible g M↦N)
sim (⇑≤⇑ g M≤M′) (ξ ([ E ]⇑ .g) M↦N)
    with sim M≤M′ (ξ E M↦N)
... |  N′ , M′—↠N′ , N≤N′
    =  N′ ⇑ g , ξ* ([ □ ]⇑ g) M′—↠N′ , ⇑≤⇑ g N≤N′
sim (≤⇑ g M≤M′) M—→N
    with sim M≤M′ M—→N
... |  N′ , M′—↠N′ , N≤N′
    =  N′ ⇑ g , ξ* ([ □ ]⇑ g) M′—↠N′ , ≤⇑ g N≤N′
sim (cast≤ e M≤M′) (ξ (`cast ∓s [ E ]) M↦N)
    with sim M≤M′ (ξ E M↦N)
... |  N′ , M′—↠N′ , N≤N′
    =  N′ , M′—↠N′ , cast≤ e N≤N′
sim (cast≤ {±p = ±p}{q = q}{r = r} e V≤M′) (ξ □ (ident e′ v))
  = ? {-
    rewrite ident≤ ±p e′ e
    =  _ , (_ ∎) , V≤M′ -}
sim (cast≤ {q = ⟨ _ ⟩ id} e V≤M′) (ξ □ (wrap e′))
    with catchup (ƛ _) V≤M′
... |  V′ , ƛ _ , M′—↠V′ , ƛN≤ƛN′
    =  V′ , M′—↠V′ , wrap≤ e′ {! e !} (gvalue≤gvalue (ƛ _) (ƛ _) ƛN≤ƛN′)
sim (cast≤ {q = ⟨ _ ⟩ _ ⇒ _} e V≤M′) (ξ □ (wrap e′))
    with catchup (ƛ _) V≤M′
... |  V′ , ƛ _ , M′—↠V′ , ƛN≤ƛN′
    =  V′ , M′—↠V′ , wrap≤ e′ {! e !} (gvalue≤gvalue (ƛ _) (ƛ _) ƛN≤ƛN′)
sim (cast≤ {q = ⟨ _ ⟩ (q ⇑ ★⇒★)} e V≤M′) (ξ □ (wrap e′))
    with catchup (ƛ _) V≤M′
... |  V′ ⇑ ★⇒★ , (ƛ _) ⇑ ★⇒★ , M′—↠V′⇑ , ≤⇑ ★⇒★ ƛN≤ƛN′
    =  V′ ⇑ ★⇒★ , M′—↠V′⇑ , ≤⇑ ★⇒★ (wrap≤ e′ {! drop⇑ e !} (gvalue≤gvalue (ƛ _) (ƛ _) ƛN≤ƛN′))
sim (cast≤ {M = V} {±p = + ⟨ _ ⟩ (p ⇑ .g)} {q = ⟨ _ ⟩ id} {r = r} refl V≤M′) (ξ □ (expand v g))
    with catchup v V≤M′
... |  V′ ⇑ .g , v′ ⇑ .g , M′—↠V′⇑ , ≤⇑ _ V≤V′
    =  V′ ⇑ g , M′—↠V′⇑ , ⇑≤⇑ g (cast≤ refl V≤V′)
sim (cast≤ {M = V} {±p = + ⟨ _ ⟩ (p ⇑ .g)} {q = ⟨ _ ⟩ (q ⇑ h)} refl V≤M′) (ξ □ (expand v g))
    =  ⊥-elim (¬★≤G h q)
sim (cast≤ {M = V ⇑ .g} {±p = - ⟨ _ ⟩ (p ⇑ .g)} {r = ⟨ _ ⟩ id} refl V⇑≤M′) (ξ □ (collapse v g))
   with catchup (v ⇑ g) V⇑≤M′
... |  V′ ⇑ .g , v′ ⇑ .g , M′—↠V′⇑ , ⇑≤⇑ .g V≤V′
    =  V′ ⇑ g , M′—↠V′⇑ , ≤⇑ g (cast≤ refl V≤V′)
sim (cast≤ {M = V ⇑ .g} {±p = - ⟨ _ ⟩ (p ⇑ .h)} {r = ⟨ _ ⟩ id} refl V⇑≤M′) (ξ □ (collide v g h G≢H))
    =  _ , (_ ∎) , blame≤
sim (cast≤ {M = V ⇑ .g} {±p = - ⟨ _ ⟩ (p ⇑ .g)} {r = ⟨ _ ⟩ (r ⇑ h)} refl V⇑≤M′) (ξ □ (collapse v g))
    =  ⊥-elim (¬★≤G h r)
sim (cast≤ {M = V ⇑ .g} {±p = - ⟨ _ ⟩ (p ⇑ .h)} {r = ⟨ _ ⟩ (r ⇑ h′)} refl V⇑≤M′) (ξ □ (collide v g h G≢H))
    =  ⊥-elim (¬★≤G h′ r)
sim (≤cast {±q = ±q} e M≤M′) M—→N
    with sim M≤M′ M—→N
... |  N′ , M′—↠N′ , N≤N′
    =  cast ±q N′ , ξ* (`cast ±q [ □ ]) M′—↠N′ , ≤cast e N≤N′
sim blame≤ M—→N
    =  ⊥-elim (blame-irreducible M—→N)
sim (wrap≤ i e V≤V′) M—→N
    =  ⊥-elim (value-irreducible (ƛ _) M—→N)
sim (≤wrap i e V≤V′) M—→N
    =  ⊥-elim (value-irreducible (ƛ _) M—→N)
sim (cast≤ e M≤M′) (ξ □ (castᵉ-blame e∌F ¬e//𝐸 v refl))
    =  _ , (_ ∎) , blame≤
sim (perform≤perform M≤M′) (ξ (″perform _ [ 𝐸 ] _) M↦N)
    with sim M≤M′ (ξ 𝐸 M↦N)
... |  N′ , M′—↠N′ , N≤N′
    = perform- _ _ N′ , ξ* (″perform _ [ □ ] _) M′—↠N′ , perform≤perform N≤N′
sim (perform≤perform M≤M′) (ξξ □ refl _ ())
sim (handle≤handle H≤ M≤) (ξ (′handle _ [ 𝐸 ]) M↦N)
    with sim M≤ (ξ 𝐸 M↦N)
... |  N′ , M′—↠N′ , N≤N′
    = handle _ N′ , ξ* (′handle _ [ □ ]) M′—↠N′ , handle≤handle H≤ N≤N′
sim (handle≤handle H≤ V≤M′) (ξ □ (handle-value v))
    with catchup v V≤M′
... | V′ , v′ , M′—↠V′ , V≤V′
    = _ , (ξ* (′handle _ [ □ ]) M′—↠V′ ++↠ unit (handle-value v′))
        , []≤[] (on-return H≤) (gvalue≤gvalue v v′ V≤V′)
sim (handle≤handle H≤ M≤) (ξ □ (handle-perform {𝐸 = 𝐸} v ¬e//𝐸 eq))
    with catchup-⟦perform⟧≤ v 𝐸 M≤ ¬e//𝐸 | lookup-All₂′ (on-perform H≤) eq
... | Mk v′ V≤V′ 𝐸≤ ¬e//𝐸′ M′—↠N′ | _ , eq′ , _ , dom≡ , cod≡ , HM′≤
    = _ , (ξ* (′handle _ [ □ ]) M′—↠N′ ++↠ unit (handle-perform v′ ¬e//𝐸′ eq′))
        , []≤[] ([]≤[] HM′≤ (ƛ≤ƛ (handle≤handle (lift≤ʰ (lift≤ʰ (subst (_ ⊢ _ ≤ _ ⦂ _ ➡_) (sym cod≡) H≤)))
                                                (⟦⟧≤⟦⟧ (lift≤ᶠ (lift≤ᶠ 𝐸≤)) (`≤` (subst (λ A → _ ⹁ A ⊢ _ ≤ˣ _ ⦂ _) (sym dom≡) Z≤Z))))))
                (gvalue≤gvalue v v′ V≤V′)
```

## Simulation extended to sequences

```
sim* : ∀ {Γ Γ′ P P′ M M′ N} {Γ≤ : Γ ≤ᴳ Γ′} {p : P ≤ᶜ P′}
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ p
  → M —↠ N
    -----------------------------------------
  → ∃[ N′ ]((M′ —↠ N′) × (Γ≤ ⊢ N ≤ᴹ N′ ⦂ p))
sim* M≤M′ (_ ∎)
    =  _ , (_ ∎) , M≤M′
sim* L≤L′ (L —→⟨ L—→M ⟩ M—↠N)
    with sim L≤L′ L—→M
... |  M′ , L′—↠M′ , M≤M′
    with sim* M≤M′ M—↠N
... |  N′ , M′—↠N′ , N≤N′
    =  N′ , (L′—↠M′ ++↠ M′—↠N′) , N≤N′
```

The gradual guarantee for reduction to a value.
```
gg : ∀ {Γ Γ′ P P′ M M′ V} {Γ≤ : Γ ≤ᴳ Γ′} {p : P ≤ᶜ P′}
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ p
  → M —↠ V
  → Value V
    ---------------------------------------------------
  → ∃[ V′ ](Value V′ × (M′ —↠ V′) × (Γ≤ ⊢ V ≤ᴹ V′ ⦂ p))
gg M≤M′ M—↠V v
    with sim* M≤M′ M—↠V
... |  N′ , M′—↠N′ , V≤N′
    with catchup v V≤N′
... |  V′ , v′ , N′—↠V′ , V≤V′
    =  V′ , v′ , (M′—↠N′ ++↠ N′—↠V′) , V≤V′
```


## Example {#example-sim}

In our running example, we showed how to increment two and its
imprecise equivalent, and computed the reduction sequences for each,
and also showed that the two original terms are related.  Applying
the gradual guarantee to the more precise reduction sequence yields
the more precise reduction sequence.

Recall the example from the end of Core, where we define
the following:

  * `inc`, the increment function
  * `inc★`, the type erasure of the increment function
  * `inc★′`, the increment function upcast to type `★`
  * `inc2—↠3`, the reduction sequence `inc · 2 —↠ $ 3`
  * `inc★2★—↠3★`, the reduction sequence `inc★ ·★ ($★ 2) —↠ $★ 3`
  * `inc★′2★—↠3★`, the reduction sequence `inc★′ ·★ ($★ 2) —↠ $★ 3`

And at the example at the end of Prec we provide

  * `inc2≤inc★2★`, evidence that `∅ ⊢ inc2 ≤ᴹ inc★2★ ⦂ ℕ≤★`.
  * `inc2≤inc★′2★`, evidence that `∅ ⊢ inc2 ≤ᴹ inc★′2★ ⦂ ℕ≤★`.

Applying `gg` to `inc2≤inc★2★`, `inc2—↠3`, and evidence that `3`
yields the reduction sequence `inc★2★—↠3★`, and similarly for
`inc★′2★`.
```
_ : gg inc2≤inc★2★ inc2—↠3 ($ 3) ≡
      ($★ 3 , $ 3 ⇑ $ℕ , inc★2★—↠3★ , $≤$★ 3)
_ = {! refl !}

{-
_ : gg inc2≤inc★′2★ inc2—↠3 ($ 3) ≡
      ($★ 3 , $ 3 ⇑ $ℕ , inc★′2★—↠3★ , $≤$★ 3)
_ = refl
-}
```
