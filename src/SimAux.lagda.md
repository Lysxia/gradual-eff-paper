## Proof of the Gradual Guarantee

```
module SimAux where

open import Utils
open import Type
open import Core
open import Progress
open import Prec
```

We now prove the gradual guarantee:
if `M ≤ᴹ M′` and `M —→ N`, then `M′ —→ N′`
and `N ≤ᴹ N′`.

## Right cast lemma

The right cast lemma says that when the term on the left of `≤ᴹ` is a value,
reducing a cast on the right preserves precision.
If `V ≤ᴹ V′`, then `cast ±q V′ —↠ W` and `V ≤ᴹ W`.
```
cast-lemma : ∀ {Γ Γ′ A B C} {Γ≤ : Γ ≤ᴳ Γ′} {p : A ≤ᶜ B} {r : A ≤ᶜ C}
           {V : Γ ⊢ A} {V′ : Γ′ ⊢ B}
  → Value V
  → Value V′
  → (±q : B =>ᶜ C)
  → ≤commuteᶜ p ±q r
  → Γ≤ ⊢ V ≤ᴹ V′ ⦂ p
    -------------------------------------------------------
  → ∃[ W ] Value W × (cast ±q V′ —↠ W) × (Γ≤ ⊢ V ≤ᴹ W ⦂ r)
```

Mirroring `progress±`, this proof proceeds by case analysis on the shape of the
cast.
```
cast-lemma v v′ ±q e V≤V′ with splitᶜ ±q in e′
```

If `±q` is the identity cast, then the cast is removed.
```
cast-lemma {p = ⟨ _ ⟩ _}  v v′ ±q e V≤V′ | id
    rewrite ≤ident ±q e′ e
    =  _ , gValue v′ , unit (ident e′ v′) , ≤gvalue v v′ V≤V′
```

If `±q` is a function cast, the value is wrapped.
```
cast-lemma (ƛ _) (ƛ _) ±q e ƛN≤ƛN′ | ∓s ⇒ ±t
    =  ƛ _ , ƛ _ , unit (wrap e′) , ≤wrap e′ (≤returns e) (gvalue≤gvalue (ƛ _) (ƛ _) ƛN≤ƛN′)
```

If `±q` is a box upcast `q ⇑ g`, the value is boxed,
and that box is related to the left-hand side using `≤⇑`.
```
cast-lemma v v′ (+ ⟨ E≤E′ ⟩ (q ⇑ g)) refl V≤V′ | other
    with cast-lemma v v′ (+ ⟨ E≤E′ ⟩ q) refl V≤V′
... |  W′ , w , V′+—↠W′ , V≤W′
    =  (W′ ⇑ g) , (w ⇑ g) , (unit (expand v′ g) ++↠ ξ* ([ □ ]⇑ g) V′+—↠W′) , ≤⇑ g V≤W′
```

For a box downcast `(- (q ⇑ g))`, the cast value must be a box `(v′ ⇑ g)`.
The commutative diagram ensures that the tag `g` in the cast matches the tag in the box.
```
cast-lemma v (v′ ⇑ g) (- ⟨ E′≤E ⟩ (q ⇑ .g)) refl (≤⇑ .g  V≤V′) | other
    with cast-lemma v v′ (- ⟨ E′≤E ⟩ q) refl V≤V′
... |  W′ , w′ , V′-—↠W′ , V≤W′
    =  W′ , w′ , (unit (collapse v′ g) ++↠ V′-—↠W′) , V≤W′
```

## Catch up lemma

The catch up lemma says that once the left side is a value, the right side must also step to
a value. If `V ≤ᴹ M′` then `M′ —↠ V′` and `V ≤ᴹ V′` for some `V′`.
```
catchup : ∀ {Γ Γ′ A A′} {Γ≤ : Γ ≤ᴳ Γ′} {p : A ≤ᶜ A′} {V : Γ ⊢ A} {M′ : Γ′ ⊢ A′}
  → Value V
  → Γ≤ ⊢ V ≤ᴹ M′ ⦂ p
    ----------------------------------------------------
  → ∃[ V′ ](Value V′ × (M′ —↠ V′) × (Γ≤ ⊢ V ≤ᴹ V′ ⦂ p))
```

When the right side is already a value, we are done.
```
catchup (ƛ _) (ƛ≤ƛ {N′ = N′} ƛN≤ƛN′)
    =  ƛ N′ , ƛ N′ , (ƛ N′ ∎) , ƛ≤ƛ ƛN≤ƛN′
catchup ($ _) ($≤$ k)
    =  $ k , $ k , ($ k ∎) , ($≤$ k)
```

When the right side is a box (whether via `⇑≤⇑` or `≤⇑`),
we reduce its contents, and a boxed value is a value.
```
catchup (v ⇑ g) (⇑≤⇑ {M = V} {M′ = M′} .g V≤M′)
    with catchup v V≤M′
... |  V′ , v′ , M′—↠V′ , V≤V′
    =  V′ ⇑ g , v′ ⇑ g , ξ* ([ □ ]⇑ g) M′—↠V′ , ⇑≤⇑ g V≤V′
catchup v (≤⇑ h V≤M′)
    with catchup v V≤M′
... |  V′ , v′ , M′—↠V′ , V≤V′
    =  V′ ⇑ h , v′ ⇑ h , ξ* ([ □ ]⇑ h) M′—↠V′ , ≤⇑ h V≤V′
```

When the right side is a cast, we reduce the cast computation, and call
`cast-lemma` to reduce the cast itself.
```
catchup v (≤cast {M′ = M′} {±q = ±q} e V≤M′)
    with catchup v V≤M′
... |  V′ , v′ , M′—↠V′ , V≤V′
    with cast-lemma v v′ ±q e V≤V′
... |  W , w , V⟨±q⟩—↠W , V≤W
    =  W , w , (ξ* (`cast ±q [ □ ]) M′—↠V′ ++↠ V⟨±q⟩—↠W) , V≤W
```

`ƛ-wrap` is already a value.
```
catchup (ƛ _) (wrap≤ e′ e ƛN≤ƛN′)
    =  _ , ƛ _ , (_ ∎) , wrap≤ e′ e ƛN≤ƛN′
catchup (ƛ _) (≤wrap e′ e ƛN≤ƛN′)
    =  _ , ƛ _ , (_ ∎) , ≤wrap e′ e ƛN≤ƛN′
```

The following lemma formalizes the intuition that substituting for a variable
which does not occur in a term yields the same term. `lift V` extends `V` with a fresh
variable in its context, which thus does not occur in `V`, and the
substitution operator `_[_]` substitutes for that variable.
```
lift[] : ∀ {Γ A P}
  → (V : Γ ⊢ P)
  → (W : ∀ {E} → Γ ⊢ ⟨ E ⟩ A)
    --------------------
  → (lift V) [ W ] ≡ V
lift[] {Γ = Γ} V W = trans (sub∘ren σ∘ V) (subId σId V)
  where
  σ∘ : ∀ {A E} (x : Γ ∋ A) → σ₀ W {E} (S x) ≡ ` x
  σ∘ x = refl
  σId : ∀ {A} {E : Effect} (x : Γ ∋ A) → _≡_ {A = _ ⊢ ⟨ _ ⟩ _} (`_ {E = E} x) (` x)  -- TODO what's going on with inference here
  σId x = refl
```

The following lemma describes β-reduction of the application of a
`ƛ-wrap` value, using the lemma above to simplify the right-hand side of the
reduction as required.

```
wrapβ : ∀ {Γ A B E A′ B′ E′ ∓s} {±t : ⟨ E ⟩ B =>ᶜ ⟨ E′ ⟩ B′} {V : ∀ {F} → Γ ⊢ ⟨ F ⟩ (A ⇒ ⟨ E ⟩ B)} {W : Γ ⊢ ⟨ E′ ⟩ A′} {±p : A ⇒ ⟨ E ⟩ B => A′ ⇒ ⟨ E′ ⟩ B′}
  → split ±p ≡ ∓s ⇒ ±t
  → (w : Value W)
    ---------------------------------------------------------------
  → ƛ-wrap ∓s ±t V · W —→ cast ±t (V · cast (pure± ∓s) (gvalue w))
wrapβ {∓s = ∓s}{±t = ±t}{V = V}{W} e w  =
  subst
    (λ X → ƛ-wrap ∓s ±t V · W —→ cast ±t (X · (cast (pure± ∓s) (gvalue w))))
    (lift[] V (gvalue w))
    (ξ □ (β w))
```

## β-reduction is a simulation

Given a `β`-reduction step `(ƛ N) W ↦ N [ gvalue w ]` on the left of an
inequality `(ƛ N) · W ≤ᴹ (ƛ N′) · W′`, we construct a reduction sequence on the
right, `(ƛ N′) · W′ —↠ M′` such that the reducts are related `N [ gvalue w] ≤ᴹ M′`.
```
simβ : ∀ {Γ Γ′ A A′ B B′ E E′} {Γ≤ : Γ ≤ᴳ Γ′} {p : A ⇒  ⟨ E ⟩ B ≤ A′ ⇒  ⟨ E′ ⟩ B′} {E≤ : E ≤ᵉ E′}
    {N : Γ ▷ A ⊢ ⟨ E ⟩ B} {N′ : Γ′ ▷ A′ ⊢ ⟨ E′ ⟩ B′} {W : Γ ⊢ ⟨ E ⟩ A} {W′ : Γ′ ⊢ ⟨ E′ ⟩ A′}
  → (w  : Value W)
  → (w′ : Value W′)
  → Γ≤ ⊢ ƛ N ≤ᴹ ƛ N′ ⦂ ⟨ E≤ ⟩ p
  → Γ≤ ⊢ W ≤ᴹ W′ ⦂ ⟨ E≤ ⟩ dom p
    -----------------------------------------------------------
  → ∃[ M′ ](((ƛ N′) · W′ —↠ M′) × (Γ≤ ⊢ N [ gvalue w ] ≤ᴹ M′ ⦂ cod p))
```

Proceed by induction on the derivation of `ƛ N ≤ᴹ ƛ N′`. There
are three rules to consider: `ƛ≤ƛ`, `wrap≤`, and `≤wrap`.

In the `ƛ≤ƛ` case, the bodies of the abstractions are related `N ≤ᴹ N′`,
so we can take a `β` step on the right, and conclude with the
following derivation:

                                ------ W≤W′
                                W ≤ W′
    ------ N≤N′   -------------------- gvalue≤gvalue
    N ≤ N′        gvalue w ≤ gvalue w′
    ---------------------------------- []≤[]
    N [ gvalue w ] ≤ᴹ N′ [ gvalue w′ ]

```
simβ {W′ = W′} w w′ (ƛ≤ƛ {N′ = N′} N≤N′) W≤W′
    =  _ ,
       (begin
         (ƛ N′) · W′   —→⟨ ξ □ (β w′) ⟩    N′ [ gvalue w′ ]
        ∎) ,
       []≤[] N≤N′ (gvalue≤gvalue w w′ W≤W′)
```

In the `wrap≤` case, the reduct on the left is an application
interspersed with casts.

    ƛ-wrap ∓s ±t (ƛ N) · W               —↠⟨ ξ □ (β w) ⟩
    cast ±t ((ƛ N) · cast ∓s (gvalue w))

We take no step on the right by giving the empty reduction sequence `_ ∎`,
and we construct the following precision derivation using the rule for
applications `·≤·` and for casts on the left `cast≤`:

                                                ------ W≤W′
                                                W ≤ W′
                                         ------------- gvalue≤
                                         gvalue w ≤ W′
         ---------- ƛN≤ƛN′     ----------------------- cast≤
         ƛ N ≤ ƛ N′            cast ∓s (gvalue w) ≤ W′
         --------------------------------------------- ·≤·
             (ƛ N) · cast ∓s (gvalue w)  ≤ (ƛ N′) · W′
    ------------------------------------------------- cast≤
    cast ±t ((ƛ N) · cast ∓s (gvalue w)) ≤ (ƛ N′) · W′

```
simβ {W = W}{W′} w w′ (wrap≤ {B = ⟨ E ⟩ _} {N = N}{N′}{r = r} e′ e ƛN≤ƛN′) W≤W′
    rewrite lift[] {P = ⟨ E ⟩ _} (ƛ N) (gvalue w)
    =  (ƛ N′) · W′ , (_ ∎) , deriv
  where
    deriv =
      cast≤ (cod≤ e′ e)
        (·≤· ƛN≤ƛN′
             (cast≤ (pure≤ (dom≤ e′ e)) (gvalue≤ w w′ W≤W′)))
```

In the `≤wrap` case, the reduction sequence on the right is displayed below.
We first take a β step for the application of `ƛ-wrap` using the `wrapβ` lemma.
We reduce the subsequent value cast using `cast-lemma`.
The last step reduces an application by the induction hypothesis `simβ`.
There remains a cast that was introduced by `ƛ-wrap`,
and which is covered by the `≤wrap` rule.
```
simβ {W = W}{W′} w w′ (≤wrap {B′ = ⟨ E′ ⟩ _} {N = N}{N′}{p = p}{r = r}{∓s = ∓s}{±t = ±t} e′ e ƛN≤ƛN′) W≤W′
    with cast-lemma w (gValue w′) (pure± ∓s) (≤pure {E≤F = _≤ᶜ_.effects (cod p)} (≤dom e′ e)) (≤gvalue w w′ W≤W′)
... |  W″ , w″ , W′-—↠W″ , W≤W″
    with simβ w w″ ƛN≤ƛN′ W≤W″
... |  M′ , [ƛN′]·W″—↠M′ , N[W]≤M′
    =  _ ,
       (begin
          ƛ-wrap ∓s ±t (ƛ N′) · W′ —→⟨ wrapβ {V = ƛ N′} e′ w′ ⟩
          cast ±t ((ƛ N′) · cast (pure± ∓s) (gvalue w′))
                                   —↠⟨ ξ* (`cast _ [ (ƛ _) ·[ □ ] ]) W′-—↠W″ ⟩
          cast ±t ((ƛ N′) · W″)    —↠⟨ ξ* (`cast _ [ □ ]) [ƛN′]·W″—↠M′ ⟩
          cast ±t M′
        ∎) ,
       (≤cast (≤cod e′ e) N[W]≤M′)
```

## Right cast lemma

The right cast lemma completes the simulation diagram for a step from a `cast` term.

```
cast≤-lemma : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᴳ Γ′} {P Q P′} {±p : P =>ᶜ Q} {Q≤P′ : Q ≤ᶜ P′} {P≤P′ : P ≤ᶜ P′} {M N M′}
  → commute≤ᶜ ±p Q≤P′ P≤P′
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ P≤P′
  → cast ±p M ↦ N
  → ∃[ N′ ] (M′ —↠ N′) × Γ≤ ⊢ N ≤ᴹ N′ ⦂ Q≤P′
```

Proof by case analysis on the derivation of `cast ±p M ↦ N`.
In each of those cases except the last one, `M` is actually a value `V`.
We apply `catchup` to reduce `M′` to a value `V′` such that `V ≤ V′`,
which we can wrap into an inequality between the reduct of `cast ± V` and `V′`.

The application of `catchup` in this lemma is made necessary by the presence of effects
in our type system. Otherwise, the `ident` rule would reduce
`cast ±p V` to `V`, and we could conclude immediately with `V≤M′`.
```
cast≤-lemma {Q≤P′ = ⟨ _ ⟩ B≤} comm V≤M′ (ident eq v)
    with catchup v V≤M′
... | V′  , v′ , M′—↠V′ , V≤V′
    rewrite ident≤ _ eq comm
    =  V′ , M′—↠V′ ,  gvalue≤ v v′ V≤V′ 
```

```
cast≤-lemma {Q≤P′ = ⟨ _ ⟩ B≤} comm V≤M′ (wrap eq)
    with B≤ | catchup (ƛ _) V≤M′
... | B≤ |  V′ , ƛ _ , M′—↠V′ , ƛN≤ƛN′
    =  V′ , M′—↠V′ , wrap≤ eq (returns≤ comm) (gvalue≤gvalue (ƛ _) (ƛ _) ƛN≤ƛN′)
... | B≤ ⇑ ★⇒★ |  V′ ⇑ ★⇒★ , (ƛ _) ⇑ ★⇒★ , M′—↠V′⇑ , ≤⇑ ★⇒★ ƛN≤ƛN′
    =  V′ ⇑ ★⇒★ , M′—↠V′⇑ , ≤⇑ ★⇒★ (wrap≤ eq (drop⇑ (returns≤ comm)) (gvalue≤gvalue (ƛ _) (ƛ _) ƛN≤ƛN′))
```

```
cast≤-lemma {±p = + ⟨ _ ⟩ (p ⇑ .g)} {Q≤P′ = ⟨ _ ⟩ id} refl V≤M′ (expand v g)
    with catchup v V≤M′
... |  V′ ⇑ .g , v′ ⇑ .g , M′—↠V′⇑ , ≤⇑ .g V≤V′
    =  V′ ⇑ g , M′—↠V′⇑ , ⇑≤⇑ g (cast≤ refl V≤V′)
```

```
cast≤-lemma {±p = + ⟨ _ ⟩ (p ⇑ .g)} {Q≤P′ = ⟨ _ ⟩ (q ⇑ h)} refl V≤M′ (expand v g)
    =  ⊥-elim (¬★≤G h q)
```

```
cast≤-lemma {±p = - ⟨ _ ⟩ (p ⇑ .g)} {P≤P′ = ⟨ _ ⟩ id} {M = W ⇑ .g} refl V≤M′ (collapse w g)
   with catchup (w ⇑ g) V≤M′
... |  W′ ⇑ .g , w′ ⇑ .g , M′—↠W′⇑ , ⇑≤⇑ .g W≤W′
    =  W′ ⇑ g , M′—↠W′⇑ , ≤⇑ g (cast≤ refl W≤W′)
```

```
cast≤-lemma {±p = - ⟨ _ ⟩ (p ⇑ .g)} {P≤P′ = ⟨ _ ⟩ (r ⇑ h)} {M = W ⇑ .g} refl V≤M′ (collapse v g)
    =  ⊥-elim (¬★≤G h r)
```

The two rules for raising blame are `collide` and `blameᵉ`.
When the left-hand side of an inequality raises blame,
there are no guarantees about the right-hand side.
```
cast≤-lemma refl V≤M′ (collide v g h G≢H)
    =  _ , (_ ∎) , blame≤
cast≤-lemma comm M≤M′ (blameᵉ e∌F ¬e//ℰ v refl)
    =  _ , (_ ∎) , blame≤
```

## Catchup lemma for operations

The following catchup lemma applies when the left side of an inequality
is a pending operation, of the form `ℰ ⟦ perform e∈E V ⟧`. In contrast the previous
`catchup` lemma applies when the left side of an inequality is a value.


The conclusion of the lemma is a fairly large conjunction.
We declare a data type for it, to hide existential witnesses which
can be inferred from the other conjuncts.
```
data CatchupPerform {Γ Γ′} (Γ≤ : Γ ≤ᴳ Γ′) {P P′} (P≤ : P ≤ᶜ P′) {E}
       e (ℰ : Frame Γ (⟨ E ⟩ response e) P) (V : Γ ⊢ ⟨ E ⟩ request e) (M′ : Γ′ ⊢ P′) : Set where
  Mk : ∀ {E′} {E≤ : E ≤ᵉ E′} {e∈E′ : e ∈☆ E′} {V′}
         {ℰ′ : Frame Γ′ (⟨ E′ ⟩ response e) P′}
    → Value V′
    → Γ≤ ⊢ V ≤ᴹ V′ ⦂ ⟨ E≤ ⟩ id
    → Γ≤ ⊢ ⟨ E≤ ⟩ id ⇒ᶠ P≤ ∋ ℰ ≤ ℰ′
    → ¬ handled e ℰ′
    → M′ —↠ ℰ′ ⟦ perform e∈E′ V′ ⟧
    → CatchupPerform Γ≤ P≤ e ℰ V M′
```

The term on the right side of the inequality `ℰ ⟦ perform e∈E V ⟧ ≤ M′` must
step to a pending operation `ℰ′ ⟦ perform e∈E′ V′ ⟧`, where each subterm
is related to the corresponding one on the left. The performed operation
`e` must be the same on both sides (definitionally), and it must not be
handled by the frame `ℰ′`.
\lyx{This is quite similar to catchup. should we still explain it?}
```
catchup-⟦perform⟧≤ : ∀ {Γ Γ′ E P P′ e} {e∈E : e ∈☆ E}
    {Γ≤ : Γ ≤ᴳ Γ′} {P≤ : P ≤ᶜ P′} {V M′}
    (v : Value V)
    (ℰ : Frame Γ (⟨ E ⟩ _) P)
  → Γ≤ ⊢ ℰ ⟦ perform e∈E V ⟧ ≤ᴹ M′ ⦂ P≤
  → ¬ handled e ℰ
  → CatchupPerform Γ≤ P≤ e ℰ V M′
catchup-⟦perform⟧≤ v □ (perform≤perform V≤M′) ¬e//ℰ with catchup v V≤M′
... | V′ , v′ , M′—↠V′ , V≤V′
    = Mk v′ V≤V′ □ (λ()) (ξ* (′perform _ [ □ ]) M′—↠V′)
catchup-⟦perform⟧≤ v ℰ (≤⇑ g M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ ¬e//ℰ
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ (≤⇑ ℰ≤ℰ′) ¬e//ℰ′ (ξ* ([ □ ]⇑ g) M′—↠ℰV′)
catchup-⟦perform⟧≤ {e∈E = e∈E} {P≤ = P≤} v ℰ (≤cast {±q = ±q} comm M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ ¬e//ℰ
... | Mk {ℰ′ = ℰ′} v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ (≤cast comm ℰ≤ℰ′) (¬handled-cast {±p = ±q} ℰ′ (∈-≤ (_≤ᶜ_.effects P≤) (¬handled-∈ ℰ ¬e//ℰ e∈E)) ¬e//ℰ′) (ξ* (`cast _ [ □ ]) M′—↠ℰV′)
catchup-⟦perform⟧≤ v ([ ℰ ]· M) (·≤· N≤ M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ N≤ ¬e//ℰ
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ N′—↠ℰV′
    = Mk v′ V≤V′ ([ ℰ≤ℰ′ ]· M≤) ¬e//ℰ′ (ξ* ([ □ ]· _) N′—↠ℰV′)
catchup-⟦perform⟧≤ v (w ·[ ℰ ]) (·≤· N≤ M≤) ¬e//ℰ
  with catchup w N≤
... | W′ , w′ , N′—↠W′ , W≤
  with catchup-⟦perform⟧≤ v ℰ M≤ ¬e//ℰ
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ ((w , w′ , W≤) ·[ ℰ≤ℰ′ ]) ¬e//ℰ′ (ξ* ([ □ ]· _) N′—↠W′ ++↠ ξ* (w′ ·[ □ ]) M′—↠ℰV′)
catchup-⟦perform⟧≤ v ([ ℰ ]⦅ f ⦆ N) (⦅⦆≤⦅⦆ .f M≤ N≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ ¬e//ℰ
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ ([ ℰ≤ℰ′ ]⦅ f ⦆ N≤) ¬e//ℰ′ (ξ* ([ □ ]⦅ f ⦆ _) M′—↠ℰV′)
catchup-⟦perform⟧≤ v (w ⦅ f ⦆[ ℰ ]) (⦅⦆≤⦅⦆ .f M≤ N≤) ¬e//ℰ
  with catchup w M≤
... | W′ , w′ , M′—↠W′ , W≤
  with catchup-⟦perform⟧≤ v ℰ N≤ ¬e//ℰ
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ N′—↠ℰV′
    = Mk v′ V≤V′ ((w , w′ , W≤) ⦅ f ⦆[ ℰ≤ℰ′ ]) ¬e//ℰ′
         (ξ* ([ □ ]⦅ f ⦆ _) M′—↠W′ ++↠ ξ* (w′ ⦅ f ⦆[ □ ]) N′—↠ℰV′)
catchup-⟦perform⟧≤ v ([ ℰ ]⇑ g) (⇑≤⇑ .g M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ ¬e//ℰ
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ ([ ℰ≤ℰ′ ]⇑ g) ¬e//ℰ′ (ξ* ([ □ ]⇑ g) M′—↠ℰV′)
catchup-⟦perform⟧≤ v (`cast ±p [ ℰ ]) (cast≤ comm M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ (¬e//ℰ ∘ inj₂)
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ (cast≤ comm ℰ≤ℰ′) ¬e//ℰ′ M′—↠ℰV′
catchup-⟦perform⟧≤ {e∈E = e∈E} {P≤ = ⟨ F≤ ⟩ _} v (`cast ±p [ ℰ ]) (*≤* {P′⊑Q′ = P′⊑Q′} M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ (¬e//ℰ ∘ inj₂)
... | Mk {ℰ′ = ℰ′} v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ (*≤* ℰ≤ℰ′) ¬e//cast[ℰ′] (ξ* (`cast _ [ □ ]) M′—↠ℰV′)
  where ¬e//cast[ℰ′] = ¬handled-cast {±p = * P′⊑Q′} ℰ′ (∈-≤ F≤ (¬handled-∈ (`cast ±p [ ℰ ]) ¬e//ℰ e∈E)) ¬e//ℰ′
catchup-⟦perform⟧≤ v (″perform e∈E [ ℰ ] eq) (perform≤perform M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ ¬e//ℰ
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ (″perform _ [ ℰ≤ℰ′ ] _) ¬e//ℰ′ (ξ* (″perform _ [ □ ] _) M′—↠ℰV′)
catchup-⟦perform⟧≤ v (′handle H [ ℰ ]) (handle≤handle {H′ = H′} H≤ M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ (¬e//ℰ ∘ inj₂)
... | Mk {ℰ′ = ℰ′} v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ (′handle H≤ [ ℰ≤ℰ′ ]) (¬handled-handle {H = H′} ℰ′ (subst (λ Eh → ¬ _ ∈ Eh) (Hooks-≤ H≤) (¬e//ℰ ∘ inj₁)) ¬e//ℰ′) (ξ* (′handle _ [ □ ]) M′—↠ℰV′)
  where
    Hooks-≤ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᴳ Γ′} {P P′} {P≤ : P ≤ᶜ P′} {Q Q′} {Q≤ : Q ≤ᶜ Q′} {H H′}
      → Γ≤ ⊢ H ≤ H′ ⦂ P≤ ⇒ʰ Q≤
      → Hooks H ≡ Hooks H′
    Hooks-≤ H≤ = All₂′-≡ (on-perform H≤)
```
