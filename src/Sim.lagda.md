
\iffalse
```
module Sim where

open import Utils
open import Type
open import Core
open import Progress
open import Prec
open import SimAux
open import VecPointwise2
```
\fi

## Term precision is a simulation (Gradual Guarantee)

The main lemma towards proving gradual guarantee is the following
simulation proof. If `M ≤ M′` and `M` takes a step `M —→ N`, then `M′` takes
some sequence of steps `M′ —↠ N′` to a less precise reduct `N ≤ N′`

$$
\input{figures/sim}
$$

```
sim : ∀ {Γ Γ′ A A′ E E′ M M′ N}
    {Γ≤ : Γ ≤ᴳ Γ′}
    {p : A ≤ A′}
    {E≤ : E ≤ᵉ E′}
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ E≤ ⟩ p
  → M —→ N
    -------------------------------
  → ∃[ N′ ] (M′ —↠ N′)
          × Γ≤ ⊢ N ≤ᴹ N′ ⦂ ⟨ E≤ ⟩ p
```

Proof by induction on the derivation of `M ≤ M′`.

Cases where the left term `M` is a value are vacuous,
because values are irreducible.

```
sim (`≤` x≤x′) M—→N
    =  ⊥-elim (variable-irreducible M—→N)
sim ($≤$ k) M—→N
    =  ⊥-elim (value-irreducible ($ _) M—→N)
sim (ƛ≤ƛ refl ƛN≤ƛN′) M—→N
    =  ⊥-elim (value-irreducible (ƛ _) M—→N)
sim (wrap≤ i e V≤V′) M—→N
    =  ⊥-elim (value-irreducible (ƛ _) M—→N)
sim (≤wrap i e V≤V′) M—→N
    =  ⊥-elim (value-irreducible (ƛ _) M—→N)
```

`blame` is irreducible as well.
```
sim blame≤ M—→N
    =  ⊥-elim (blame-irreducible M—→N)
```

In every other case of the derivation of `M ≤ M′`,
we proceed by case analysis on the reduction step `M —→ N`.

When the evaluation context is distinct from `□`,
the proof is relies on the induction hypothesis `sim`.
The following diagram pictures this method generally: the inner square is
given by the induction hypothesis, upon which we build the outer square using
congruence rules. In our Agda proof, this part of the proof is spelled out for
each constructor of the context `ℰ`.

$$
\input{figures/sim-ctx}
$$

For the application rule `·≤·`, this leads to three subcases.

If the reduction happens under the evaluation context `[ ℰ ]· M`,
we have `L ≤ L′`, `M ≤ M′` and `L —→ N`.
We apply the induction hypothesis on `L ≤ L′` to reduce `L′` to `N′`.
We thus reduce `L′ · M′` to `N′ · M′` and prove
`N · M′ ≤ N′ · M′` by the rule `·≤·`.

```
sim (·≤· {L′ = L′} {M′ = M′} refl L≤L′ M≤M′)
    (ξ ([ ℰ ]· M) L↦N)
    with sim L≤L′ (ξ ℰ L↦N)
... |  N′ , L′—↠N′ , N≤N′
    =  N′ · M′ ,
       (begin
         L′ · M′
           —↠⟨ ξ* ([ □ ]· _) L′—↠N′ ⟩
         N′ · M′
        ∎) ,
       ·≤· refl N≤N′ M≤M′
```

If the reduction happens under `V ·[ ℰ ]`, the left
operand `V` must be a value. We apply the `catchup` lemma
to reduce `L′ · M′` to `V′ · M′` where `V′` is a value,
and the induction hypothesis `sim` to reduce `V′ · M′` to `V′ · N′`.

```
sim (·≤· {L′ = L′} {M′ = M′} refl V≤L′ M≤M′)
    (ξ (v ·[ ℰ ]) M↦N)
    with catchup v V≤L′
... |  V′ , v′ , L′—↠V′ , V≤V′
    with sim M≤M′ (ξ ℰ M↦N)
... |  N′ , M′—↠N′ , N≤N′
    =  V′ · N′ ,
       (begin
         L′ · M′  —↠⟨ ξ* ([ □ ]· _) L′—↠V′ ⟩
         V′ · M′  —↠⟨ ξ* (v′ ·[ □ ]) M′—↠N′ ⟩
         V′ · N′
       ∎) ,
       ·≤· refl V≤V′ N≤N′
```

The last subcase for `·≤·` is `β`-reduction.
`(ƛ N) · W ≤ L′ · M′` is inverted to `ƛ N ≤ L′` and `W ≤ M′`.
By two applications of `catchup`, we reduce
`L′ · M′` to `(ƛ N′) · M′` and then to `(ƛ N′) · W′`.
by induction hypothesis `simβ`, we find the remaining steps to simulate the
reduct `N [ gvalue W ]` on the left hand side.

$$
\input{figures/sim-case-beta}
$$

```
sim (·≤· {L′ = L′} {M′ = M′} refl ƛN≤L′ V≤M′)
    (ξ □ (β v))
    with catchup (ƛ _) ƛN≤L′
... |  ƛ N′ , ƛ N′ , L′—↠ƛN′ , ƛN≤ƛN′
    with catchup v V≤M′
... |  V′ , v′ , M′—↠V′ , V≤V′
    with simβ refl v v′ ƛN≤ƛN′ V≤V′
... |  N″ , ƛN′·V′—↠N″ , N[V]≤N″
    =  N″ ,
       (begin
         L′ · M′     —↠⟨ ξ* ([ □ ]· _) L′—↠ƛN′ ⟩
         (ƛ N′) · M′
           —↠⟨ ξ* ((ƛ N′) ·[ □ ]) M′—↠V′ ⟩
         (ƛ N′) · V′ —↠⟨ ƛN′·V′—↠N″ ⟩
         N″
       ∎) ,
       N[V]≤N″
```

The case of `⦅⦆≤⦅⦆` is analogous to `·≤·`.
```
sim (⦅⦆≤⦅⦆ _⊕_ L≤L′ M≤M′)
    (ξ ([ ℰ ]⦅ ._⊕_ ⦆ _) L↦N)
    with sim L≤L′ (ξ ℰ L↦N)
... |  N′ , L′—↠N′ , N≤N′
    =  N′ ⦅ _⊕_ ⦆ _
    ,  ξ* ([ □ ]⦅ _⊕_ ⦆ _) L′—↠N′
    ,  ⦅⦆≤⦅⦆ _⊕_ N≤N′ M≤M′
sim (⦅⦆≤⦅⦆ _⊕_ V≤L′ M≤M′)
    (ξ (v ⦅ ._⊕_ ⦆[ ℰ ]) M↦N)
    with catchup v V≤L′
... |  V′ , v′ , L′—↠V′ , V≤V′
    with sim M≤M′ (ξ ℰ M↦N)
... |  N′ , M′—↠N′ , N≤N′
    =  V′ ⦅ _⊕_ ⦆ N′
    , (ξ* ([ □ ]⦅ _⊕_ ⦆ _) L′—↠V′
        ++↠ ξ* (v′ ⦅ _⊕_ ⦆[ □ ]) M′—↠N′)
    , ⦅⦆≤⦅⦆ _⊕_ V≤V′ N≤N′
sim (⦅⦆≤⦅⦆ _⊕_ V≤L′ W≤M′)
    (ξ □ δ)
    with catchup ($ _) V≤L′
... |  $ k , $ .k , L′—↠V′ , ($≤$ .k)
    with catchup ($ _) W≤M′
... |  $ k′ , $ .k′ , M′—↠W′ , ($≤$ .k′)
    =  $ (k ⊕ k′)
    , (ξ* ([ □ ]⦅ _⊕_ ⦆ _) L′—↠V′
        ++↠ ξ* ($ k ⦅ _⊕_ ⦆[ □ ]) M′—↠W′ ++↠ unit δ)
    , $≤$ (k ⊕ k′)
```

For the rule `⇑≤⇑`, the left-hand side is `M ⇑ g`, which is not a redex: the
reduction cannot happen in the empty evaluation context `□`.
```
sim (⇑≤⇑ g M≤M′) (ξ □ M↦N)
    =  ⊥-elim (box-irreducible g M↦N)
```

For a reduction under the context `[ ℰ ]⇑ g`,
we conclude by the induction hypothesis `sim`.
```
sim (⇑≤⇑ g M≤M′) (ξ ([ ℰ ]⇑ .g) M↦N)
    with sim M≤M′ (ξ ℰ M↦N)
... |  N′ , M′—↠N′ , N≤N′
    =  N′ ⇑ g , ξ* ([ □ ]⇑ g) M′—↠N′ , ⇑≤⇑ g N≤N′
```

The two cases for `≤⇑` and `≤cast` are also straightforward
consequences of the induction hypothesis, simply wrapping
right-hand side terms under `_ ⇑ g` or `cast ±q _`.
```
sim (≤⇑ g M≤M′) M—→N
    with sim M≤M′ M—→N
... |  N′ , M′—↠N′ , N≤N′
    =  N′ ⇑ g , ξ* ([ □ ]⇑ g) M′—↠N′ , ≤⇑ g N≤N′

sim (≤cast {±q = ±q} e M≤M′) M—→N
    with sim M≤M′ M—→N
... |  N′ , M′—↠N′ , N≤N′
    =  cast ±q N′
    ,  ξ* (`cast ±q [ □ ]) M′—↠N′
    ,  ≤cast e N≤N′
```

If the reduction happens under the evaluation context ``cast ±p [ ℰ ]`,
we apply the induction hypothesis.
```
sim (cast≤ e M≤M′)
    (ξ (`cast ±p [ ℰ ]) M↦N)
    with sim M≤M′ (ξ ℰ M↦N)
... |  N′ , M′—↠N′ , N≤N′
    =  N′ , M′—↠N′ , cast≤ e N≤N′
```

```
sim (castᵉ≤ M≤M′) (ξ (`castᵉ ±p [ ℰ ]) M↦N)
    with sim M≤M′ (ξ ℰ M↦N)
... | N′ , M′—↠N′ , N≤N′
    = N′ , M′—↠N′ , castᵉ≤ N≤N′
```

```
sim (castᵉ≤ M≤M′) (ξ □ (blameᵉ _ _ _ _))
    = _ , (_ ∎) , blame≤
```

```
sim (castᵉ≤ M≤M′) (ξ □ (castᵉ-return v))
    = ?
```

```
sim (≤castᵉ M≤M′) M↦N
    with sim M≤M′ M↦N
... | N′ , M′—↠N′ , N≤N′
    = ?
```

Otherwise, if the reduction happens under the evaluation context `□`,
the reduction rules that may apply are
`ident`, `wrap`, `expand`, `collapse`, `collide`, or `blameᵉ`.
```
sim (cast≤ comm M≤M′)
    (ξ □ castM↦N)
  = cast≤-lemma comm M≤M′ castM↦N
```

Reduction under `″perform _ [ ℰ ] _`.
```
sim (perform≤perform M≤M′)
    (ξ (″perform _ [ ℰ ] _) M↦N)
    with sim M≤M′ (ξ ℰ M↦N)
... |  N′ , M′—↠N′ , N≤N′
    = perform- _ N′ _
    , ξ* (″perform _ [ □ ] _) M′—↠N′
    , perform≤perform N≤N′
```

`perform` is not a redex: reduction cannot happen under context `□`.
```
sim (perform≤perform M≤M′)
    (ξξ □ refl _ ())
```

Reduction under `′handle _ [ ℰ ]`.
```
sim (handle≤handle H≤ M≤)
    (ξ (′handle _ [ ℰ ]) M↦N)
    with sim M≤ (ξ ℰ M↦N)
... |  N′ , M′—↠N′ , N≤N′
    = handle _ N′
    , ξ* (′handle _ [ □ ]) M′—↠N′
    , handle≤handle H≤ N≤N′
```

```
sim (handle≤handle H≤ V≤M′)
    (ξ □ (handle-value v))
    with catchup v V≤M′
... | V′ , v′ , M′—↠V′ , V≤V′
    = _ , (ξ* (′handle _ [ □ ]) M′—↠V′
             ++↠ unit (handle-value v′))
        , []≤[] (on-return H≤)
                (gvalue≤gvalue v v′ V≤V′)
```

```
sim (handle≤handle H≤ M≤)
    (ξ □ (handle-perform {e∈E = op∈E} {ℰ = ℰ} v ¬op//ℰ eq))
    with catchup-⟦perform⟧≤ v ℰ M≤
       | lookup-All₂′ (on-perform H≤) eq
... | Mk v′ V≤V′ ℰ≤ M′—↠N′
    | _ , eq′ , _ , dom≡ , cod≡ , HM′≤
    = _ , (ξ* (′handle _ [ □ ]) M′—↠N′
            ++↠ unit (handle-perform v′ (≤-handled ℰ≤ op∈E ¬op//ℰ) eq′))
        , []≤[]
            ([]≤[] HM′≤
              (ƛ≤ƛ refl (handle≤handle
                (lift≤ʰ (lift≤ʰ
                  (subst (_ ⊢ _ ≤ _ ⦂ _ ⇒ʰ_)
                         (sym cod≡) H≤)))
                (⟦⟧≤⟦⟧ (lift≤ᶠ (lift≤ᶠ ℰ≤))
                   (`≤` (subst
                           (λ A → _ ▷ A ⊢ _ ≤ˣ _ ⦂ _)
                           (sym dom≡) Z≤Z))))))
                (gvalue≤gvalue v v′ V≤V′)
```

## Simulation extended to sequences

```
sim* : ∀ {Γ Γ′ P P′ M M′ N}
    {Γ≤ : Γ ≤ᴳ Γ′}
    {p : P ≤ᶜ P′}
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ p
  → M —↠ N
    ---------------------------
  → ∃[ N′ ] (M′ —↠ N′)
          × (Γ≤ ⊢ N ≤ᴹ N′ ⦂ p)
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
gg : ∀ {Γ Γ′ P P′ M M′ V}
    {Γ≤ : Γ ≤ᴳ Γ′} {p : P ≤ᶜ P′}
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ p
  → M —↠ V
  → Value V
    ----------------------------
  → ∃[ V′ ] Value V′
          × (M′ —↠ V′)
          × Γ≤ ⊢ V ≤ᴹ V′ ⦂ p
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
{-
_ : gg inc2≤inc★2★ inc2—↠3 ($ 3) ≡
      ($★ 3 , $ 3 ⇑ $ℕ , inc★2★—↠3★ , $≤$★ 3)
_ = refl
-}

{-
_ : gg inc2≤inc★′2★ inc2—↠3 ($ 3) ≡
      ($★ 3 , $ 3 ⇑ $ℕ , inc★′2★—↠3★ , $≤$★ 3)
_ = refl
-}
```
