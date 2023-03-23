# Gradual Guarantee

\iffalse
```
module SimAux where

open import Utils
open import Type
open import Core
open import Progress
open import Prec
open import VecPointwise2
```
\fi

We now prove the gradual guarantee:
if `M ≤ᴹ M′` and `M —→ N`, then `M′ —→ N′`
and `N ≤ᴹ N′`.

We decompose the proof into several intermediate lemmas.

## Right cast lemma

The right cast lemma says that when the term on the left of `≤ᴹ` is a value,
reducing a cast on the right preserves precision.
If `V ≤ᴹ V′`, then `cast ±q V′ —↠ W` and `V ≤ᴹ W`.
The situation is represented by the following diagrams, depending on whether
`±q` is an upcast `+q` or downcast `-q`.

$$
\input{figures/right-cast-lemma}
$$

$$
\input{figures/right-cast-lemma-minus}
$$

```
cast-lemma : ∀ {Γ Γ′ A B C E E′}
    {Γ≤ : Γ ≤ᴳ Γ′}
    {p : A ≤ B} {r : A ≤ C} {e : E ≤ᵉ E′}
    {V : Γ ⊢ ⟨ E ⟩ A} {V′ : Γ′ ⊢ ⟨ E′ ⟩ B}
  → Value V
  → Value V′
  → (±q : B => C)
  → ≤commute p ±q r
  → Γ≤ ⊢ V ≤ᴹ V′ ⦂ ⟨ e ⟩ p
    ------------------------
  → ∃[ W ] Value W
         × (cast ±q V′ —↠ W)
         × (Γ≤ ⊢ V ≤ᴹ W ⦂ ⟨ e ⟩ r)
```

Mirroring `progress±`, this proof proceeds by case analysis on the shape of the
cast.
```
cast-lemma v v′ ±q e V≤V′ with split ±q in e′
```

If `±q` is the identity cast, then the cast is removed.
$$
\input{figures/right-cast-case-id}
$$
\lyx{the p pattern somehow helps the typechecker}
```
cast-lemma {p = _} v v′ ±q e V≤V′ | id
    rewrite ≤ident ±q e′ e
    =  _ , gValue v′
         , unit (ident e′ v′)
         , ≤gvalue v v′ V≤V′
```

If `±q` is a function cast, the value is wrapped.
$$
\input{figures/right-cast-case-fun}
$$
```
cast-lemma (ƛ _) (ƛ _) ±q e ƛN≤ƛN′ | ∓s ⇒⟨ ±e ⟩ ±t
    =  ƛ _ , ƛ _ ,
       unit (wrap e′) ,
       ≤wrap e′ e
         (gvalue≤gvalue (ƛ _) (ƛ _) ƛN≤ƛN′)
```

If `±q` is a box upcast `q ⇑ g`, the value is boxed,
and that box is related to the left-hand side using `≤⇑`.
$$
\input{figures/right-cast-case-expand}
$$
```
cast-lemma v v′ (+ (q ⇑ g)) refl V≤V′ | other
    with cast-lemma v v′ (+ q) refl V≤V′
... |  W′ , w , V′—↠W′ , V≤W′
    =  (W′ ⇑ g) , (w ⇑ g)
         , (unit (expand v′ g)
              ++↠ ξ* ([ □ ]⇑ g) V′—↠W′)
         , ≤⇑ g V≤W′
```

For a box downcast `(- (q ⇑ g))`, the cast value must be a box `(v′ ⇑ g)`.
The commutative diagram ensures that the tag `g` in the cast matches the tag in the box.
$$
\input{figures/right-cast-case-collapse}
$$
```
cast-lemma v (v′ ⇑ g) (- (q ⇑ .g)) refl (≤⇑ .g  V≤V′) | other
    with cast-lemma v v′ (- q) refl V≤V′
... |  W′ , w′ , V′—↠W′ , V≤W′
    =  W′ , w′ ,
       (unit (collapse v′ g) ++↠ V′—↠W′) ,
       V≤W′
```

## Catch up lemma

The catch up lemma says that once the left side is a value, the right side must also step to
a value. If `V ≤ᴹ M′` then `M′ —↠ V′` and `V ≤ᴹ V′` for some `V′`.

$$ \input{figures/catchup} $$

```
catchup : ∀ {Γ Γ′ A A′}
    {Γ≤ : Γ ≤ᴳ Γ′}
    {V : Γ ⊢ A} {M′ : Γ′ ⊢ A′}
    {p : A ≤ᶜ A′}
  → Value V
  → Γ≤ ⊢ V ≤ᴹ M′ ⦂ p
    ----------------------------------------------------
  → ∃[ V′ ](Value V′ × (M′ —↠ V′) × (Γ≤ ⊢ V ≤ᴹ V′ ⦂ p))
```

When the right side is already a value, we are done.

`ƛ-wrap` is also a value.
```
catchup (ƛ _) (wrap≤ e′ e ƛN≤ƛN′)
    =  _ , ƛ _ , (_ ∎) , wrap≤ e′ e ƛN≤ƛN′
catchup (ƛ _) (≤wrap e′ e ƛN≤ƛN′)
    =  _ , ƛ _ , (_ ∎) , ≤wrap e′ e ƛN≤ƛN′
```

$$ \input{figures/catchup-value} $$

```
catchup (ƛ _) (ƛ≤ƛ {N′ = N′} ƛN≤ƛN′)
    =  ƛ N′ , ƛ N′ , (ƛ N′ ∎) , ƛ≤ƛ ƛN≤ƛN′
catchup ($ _) ($≤$ k)
    =  $ k , $ k , ($ k ∎) , ($≤$ k)
```

When the right side is a box (whether via `⇑≤⇑` or `≤⇑`),
we reduce its contents, and a boxed value is a value.

$$ \input{figures/catchup-box} $$

```
catchup (v ⇑ g) (⇑≤⇑ {M = V} {M′ = M′} .g V≤M′)
    with catchup v V≤M′
... |  V′ , v′ , M′—↠V′ , V≤V′
    =  V′ ⇑ g
    ,  v′ ⇑ g
    ,  ξ* ([ □ ]⇑ g) M′—↠V′
    ,  ⇑≤⇑ g V≤V′
catchup v (≤⇑ h V≤M′)
    with catchup v V≤M′
... |  V′ , v′ , M′—↠V′ , V≤V′
    =  V′ ⇑ h
    ,  v′ ⇑ h
    ,  ξ* ([ □ ]⇑ h) M′—↠V′
    ,  ≤⇑ h V≤V′
```

When the right side is a cast, we reduce the cast computation, and call
`cast-lemma` to reduce the cast itself.
In the following diagram, the applications of `catchup` and `cast-lemma`
are respectively represented by the left and bottom commutative triangles.

$$ \input{figures/catchup-cast} $$

```
catchup v (≤cast {M′ = M′} {±q = ±q} e V≤M′)
    with catchup v V≤M′
... |  V′ , v′ , M′—↠V′ , V≤V′
    with cast-lemma v v′ ±q e V≤V′
... |  W , w , V⟨±q⟩—↠W , V≤W
    =  W , w
    , (ξ* (`cast ±q [ □ ]) M′—↠V′ ++↠ V⟨±q⟩—↠W)
    , V≤W
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
```

\iffalse
```
lift[] {Γ = Γ} V W
  = trans (sub∘ren σ∘ V) (subId σId V)
  where

  σ∘ : ∀ {A E} (x : Γ ∋ A)
    → σ₀ W {E} (S x) ≡ ` x
  σ∘ x = refl

  σId : ∀ {A} {E : Effect} (x : Γ ∋ A)
    → _≡_ {A = _ ⊢ ⟨ _ ⟩ _}
          (`_ {E = E} x) (` x)
  -- TODO what's going on with inference here
  σId x = refl
```
\fi

The following lemma describes β-reduction of the application of a
`ƛ-wrap` value, using the lemma above to simplify the right-hand side of the
reduction as required.

```
wrapβ : ∀ {Γ A B E A′ B′ E′ ∓s}
    {±t : B => B′}
    {±e : E =>ᵉ E′}
    {V : ∀ {F} → Γ ⊢ ⟨ F ⟩ (A ⇒ ⟨ E ⟩ B)}
    {W : Γ ⊢ ⟨ E′ ⟩ A′}
    {±p : A ⇒ ⟨ E ⟩ B => A′ ⇒ ⟨ E′ ⟩ B′}
  → split ±p ≡ ∓s ⇒⟨ ±e ⟩ ±t
  → (w : Value W)
    -------------------------------------
  → ƛ-wrap ∓s ±t ±e V · W
      —→ cast ±t (castᵉ ±e (V · cast ∓s (gvalue w)))
wrapβ {∓s = ∓s}{±t = ±t}{±e = ±e}{V = V}{W} e w  =
  subst
    (λ X → ƛ-wrap ∓s ±t ±e V · W
       —→ cast ±t (castᵉ ±e (X · (cast ∓s (gvalue w)))))
    (lift[] V (gvalue w))
    (ξ □ (β w))
```

## β-reduction is a simulation

Given a `β`-reduction step `(ƛ N) W ↦ N [ gvalue w ]` on the left of an
inequality `(ƛ N) · W ≤ᴹ (ƛ N′) · W′`, we construct a reduction sequence on the
right, `(ƛ N′) · W′ —↠ M′` such that the reducts are related `N [ gvalue w] ≤ᴹ M′`.

$$ \input{figures/simbeta} $$

```
simβ : ∀ {Γ Γ′ A A′ B B′ E E′}
    {Γ≤ : Γ ≤ᴳ Γ′}
    {E≤ : E ≤ᵉ E′}
    {p : A ⇒  ⟨ E ⟩ B ≤ A′ ⇒  ⟨ E′ ⟩ B′}
    {N : Γ ▷ A ⊢ ⟨ E ⟩ B}
    {N′ : Γ′ ▷ A′ ⊢ ⟨ E′ ⟩ B′}
    {W : Γ ⊢ ⟨ E ⟩ A} {W′ : Γ′ ⊢ ⟨ E′ ⟩ A′}
  → (w  : Value W)
  → (w′ : Value W′)
  → Γ≤ ⊢ ƛ N ≤ᴹ ƛ N′ ⦂ ⟨ E≤ ⟩ p
  → Γ≤ ⊢ W ≤ᴹ W′ ⦂ ⟨ E≤ ⟩ dom p
    -----------------------------------------
  → ∃[ M′ ] ((ƛ N′) · W′ —↠ M′)
          × Γ≤ ⊢ N [ gvalue w ] ≤ᴹ M′ ⦂ ⟨ eff p ⟩ cod p
```

Proceed by induction on the derivation of `ƛ N ≤ᴹ ƛ N′`. There
are three rules to consider: `ƛ≤ƛ`, `wrap≤`, and `≤wrap`.

In the `ƛ≤ƛ` case, the bodies of the abstractions are related `N ≤ᴹ N′`,
so we can take a `β` step on the right, and conclude with the
derivation in \Cref{fig:simbeta-lambda}

\begin{figure}

                                ------ W≤W′
                                W ≤ W′
    ------ N≤N′   -------------------- gvalue≤gvalue
    N ≤ N′        gvalue w ≤ gvalue w′
    ---------------------------------- []≤[]
    N [ gvalue w ] ≤ᴹ N′ [ gvalue w′ ]

$$ \input{figures/simbeta-lambda} $$

\caption{Derivation and diagram for
case `ƛ≤ƛ` of `simβ`
}
\label{fig:simbeta-lambda}
\end{figure}

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
and we construct the precision derivation in \Cref{fig:simbeta-wrapl}
using the rule for applications `·≤·` and for casts on the left `cast≤`.

\begin{figure}

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

$$ \input{figures/simbeta-wrap-left} $$

\caption{Derivation and diagram for case `wrap≤` of `simβ`}
\label{fig:simbeta-wrapl}
\end{figure}

```
simβ {W = W}{W′} w w′ (wrap≤ {E = E} {N = N}{N′}{r = r} e′ e ƛN≤ƛN′) W≤W′
    rewrite lift[] {P = ⟨ E ⟩ _} (ƛ N) (gvalue w)
    =  (ƛ N′) · W′ , (_ ∎) , deriv
  where
    deriv =
      cast≤ (cod≤ e′ e)
        (castᵉ≤
          (·≤· ƛN≤ƛN′
               (cast≤ (dom≤ e′ e) (gvalue≤ w w′ W≤W′))))
```

In the `≤wrap` case, the reduction sequence on the right is displayed in \Cref{fig:simbeta-wrapr}.
We first take a β step for the application of `ƛ-wrap` using the `wrapβ` lemma.
We reduce the subsequent value cast using `cast-lemma`.
The last step reduces an application by the induction hypothesis `simβ`.
There remains a cast that was introduced by `ƛ-wrap`,
and which is covered by the `≤wrap` rule.

\begin{figure}

$$ \input{figures/simbeta-wrap-right} $$

\caption{Diagram for case `≤wrap` of `simβ`}
\label{fig:simbeta-wrapr}
\end{figure}

```
simβ {W = W}{W′} w w′
    (≤wrap {E′ = E′} {N = N}{N′}
           {p = p}{r = r}{∓s = ∓s}{±t = ±t}{±e = ±e}
           e′ e ƛN≤ƛN′) W≤W′
    with cast-lemma w (gValue w′) ∓s (≤dom e′ e) (≤gvalue w w′ W≤W′)
... |  W″ , w″ , W′—↠W″ , W≤W″
    with simβ w w″ ƛN≤ƛN′ W≤W″
... |  M′ , [ƛN′]·W″—↠M′ , N[W]≤M′
    =  _ ,
       (begin
          ƛ-wrap ∓s ±t ±e (ƛ N′) · W′
            —→⟨ wrapβ {V = ƛ N′} e′ w′ ⟩
          cast ±t (castᵉ ±e ((ƛ N′) · cast ∓s
                                 (gvalue w′)))
            —↠⟨ ξ* (`cast _ [ `castᵉ _ [ (ƛ _) ·[ □ ] ] ])
                   W′—↠W″ ⟩
          cast ±t (castᵉ ±e ((ƛ N′) · W″))
            —↠⟨ ξ* (`cast _ [ `castᵉ _ [ □ ] ])
                   [ƛN′]·W″—↠M′ ⟩
          cast ±t (castᵉ ±e M′)
        ∎) ,
       (≤cast (≤cod e′ e) (≤castᵉ N[W]≤M′))
```

## Left cast lemma

The left cast lemma completes the simulation diagram for a step from a `cast` term.

```
cast≤-lemma : ∀ {Γ Γ′} {A A′ B E E′} {e : E ≤ᵉ E′}
    {Γ≤ : Γ ≤ᴳ Γ′} {±p : A => B} {b : B ≤ A′} {a : A ≤ A′} {M N M′}
  → commute≤ ±p b a
  → Γ≤ ⊢ M ≤ᴹ M′ ⦂ ⟨ e ⟩ a
  → cast ±p M ↦ N
  → ∃[ N′ ] (M′ —↠ N′)
          × Γ≤ ⊢ N ≤ᴹ N′ ⦂ ⟨ e ⟩ b
```

Proof by case analysis on the derivation of `cast ±p M ↦ N`.
In each of those cases except the last one, `M` is actually a value `V`.
We apply `catchup` to reduce `M′` to a value `V′` such that `V ≤ V′`,
which we can wrap into an inequality between the reduct of `cast ± V` and `V′`.

The application of `catchup` in this lemma is made necessary by the presence of effects
in our type system. Otherwise, the `ident` rule would reduce
`cast ±p V` to `V`, and we could conclude immediately with `V≤M′`.
```
cast≤-lemma comm V≤M′ (ident eq v) with catchup v V≤M′
... | V′  , v′ , M′—↠V′ , V≤V′
    rewrite ident≤ _ eq comm
    =  V′ , M′—↠V′ ,  gvalue≤ v v′ V≤V′ 
```

For `wrap`, we have two subcases depending on whether the right-hand side
reduces to an abstraction or to a box.
```
cast≤-lemma {b = b} comm V≤M′
    (wrap eq)
    with b | catchup (ƛ _) V≤M′
... | B≤
    |  V′ , ƛ _ , M′—↠V′ , ƛN≤ƛN′
    =  V′ , M′—↠V′
    , wrap≤ eq comm
        (gvalue≤gvalue (ƛ _) (ƛ _) ƛN≤ƛN′)
... | B≤ ⇑ ★⇒★
    |  V′ ⇑ ★⇒★
       , (ƛ _) ⇑ ★⇒★
       , M′—↠V′⇑ , ≤⇑ ★⇒★ ƛN≤ƛN′
    =  V′ ⇑ ★⇒★ , M′—↠V′⇑ ,
       ≤⇑ ★⇒★
        (wrap≤ eq (drop⇑ comm)
          (gvalue≤gvalue (ƛ _) (ƛ _) ƛN≤ƛN′))
```

```
cast≤-lemma {±p = + (p ⇑ .g)} {b = id} refl V≤M′ (expand v g)
    with catchup v V≤M′
... |  V′ ⇑ .g , v′ ⇑ .g
       , M′—↠V′⇑ , ≤⇑ .g V≤V′
    =  V′ ⇑ g
    , M′—↠V′⇑
    , ⇑≤⇑ g (cast≤ refl V≤V′)
```

```
cast≤-lemma {±p = + (p ⇑ .g)} {b = (q ⇑ h)} refl V≤M′ (expand v g)
    =  ⊥-elim (¬★≤G h q)
```

```
cast≤-lemma {±p = - (p ⇑ .g)} {a = id} {M = W ⇑ .g} refl V≤M′ (collapse w g)
   with catchup (w ⇑ g) V≤M′
... |  W′ ⇑ .g , w′ ⇑ .g , M′—↠W′⇑ , ⇑≤⇑ .g W≤W′
    =  W′ ⇑ g , M′—↠W′⇑ , ≤⇑ g (cast≤ refl W≤W′)
```

```
cast≤-lemma {±p = - (p ⇑ .g)} {a = (r ⇑ h)} {M = W ⇑ .g} refl V≤M′ (collapse v g)
    =  ⊥-elim (¬★≤G h r)
```

The two rules for raising blame are `collide` and `blameᵉ`.
When the left-hand side of an inequality raises blame,
there are no guarantees about the right-hand side.
```
cast≤-lemma refl V≤M′ (collide v g h G≢H)
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
data CatchupPerform {Γ Γ′} (Γ≤ : Γ ≤ᴳ Γ′)
       {P P′} (P≤ : P ≤ᶜ P′) {E} e
       (ℰ : Frame Γ (⟨ E ⟩ response e) P)
       (V : Γ ⊢ ⟨ E ⟩ request e)
       (M′ : Γ′ ⊢ P′) : Set where
  Mk : ∀ {E′} {E≤ : E ≤ᵉ E′}
      {e∈E′ : e ∈☆ E′} {V′}
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
catchup-⟦perform⟧≤ : ∀ {Γ Γ′ E P P′ e}
    {e∈E : e ∈☆ E}
    {Γ≤ : Γ ≤ᴳ Γ′} {P≤ : P ≤ᶜ P′} {V M′}
    (v : Value V)
    (ℰ : Frame Γ (⟨ E ⟩ _) P)
  → Γ≤ ⊢ ℰ ⟦ perform e∈E V ⟧ ≤ᴹ M′ ⦂ P≤
  → ¬ handled e ℰ
  → CatchupPerform Γ≤ P≤ e ℰ V M′
catchup-⟦perform⟧≤ v □ (perform≤perform V≤M′)
                   ¬e//ℰ with catchup v V≤M′
... | V′ , v′ , M′—↠V′ , V≤V′
    = Mk v′ V≤V′ □ (λ())
         (ξ* (′perform _ [ □ ]) M′—↠V′)
catchup-⟦perform⟧≤ v ℰ (≤⇑ g M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ ¬e//ℰ
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ (≤⇑ ℰ≤ℰ′) ¬e//ℰ′
         (ξ* ([ □ ]⇑ g) M′—↠ℰV′)
catchup-⟦perform⟧≤ {e∈E = e∈E} {P≤ = P≤} v ℰ
       (≤cast {±q = ±q} comm M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ ¬e//ℰ
... | Mk {ℰ′ = ℰ′} v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk  v′ V≤V′ (≤cast comm ℰ≤ℰ′) ¬e//ℰ′
          (ξ* (`cast _ [ □ ]) M′—↠ℰV′)
catchup-⟦perform⟧≤ v ([ ℰ ]· M)
                   (·≤· N≤ M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ N≤ ¬e//ℰ
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ N′—↠ℰV′
    = Mk v′ V≤V′ ([ ℰ≤ℰ′ ]· M≤) ¬e//ℰ′
         (ξ* ([ □ ]· _) N′—↠ℰV′)
catchup-⟦perform⟧≤ v (w ·[ ℰ ])
                   (·≤· N≤ M≤) ¬e//ℰ
  with catchup w N≤
... | W′ , w′ , N′—↠W′ , W≤
  with catchup-⟦perform⟧≤ v ℰ M≤ ¬e//ℰ
... | Mk   v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk   v′ V≤V′
           ((w , w′ , W≤) ·[ ℰ≤ℰ′ ]) ¬e//ℰ′
           (ξ* ([ □ ]· _) N′—↠W′
              ++↠ ξ* (w′ ·[ □ ]) M′—↠ℰV′)
catchup-⟦perform⟧≤ v ([ ℰ ]⦅ f ⦆ N)
                   (⦅⦆≤⦅⦆ .f M≤ N≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ ¬e//ℰ
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ ([ ℰ≤ℰ′ ]⦅ f ⦆ N≤) ¬e//ℰ′
         (ξ* ([ □ ]⦅ f ⦆ _) M′—↠ℰV′)
catchup-⟦perform⟧≤ v (w ⦅ f ⦆[ ℰ ])
                   (⦅⦆≤⦅⦆ .f M≤ N≤) ¬e//ℰ
  with catchup w M≤
... | W′ , w′ , M′—↠W′ , W≤
  with catchup-⟦perform⟧≤ v ℰ N≤ ¬e//ℰ
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ N′—↠ℰV′
    = Mk v′ V≤V′
         ((w , w′ , W≤) ⦅ f ⦆[ ℰ≤ℰ′ ]) ¬e//ℰ′
         (ξ* ([ □ ]⦅ f ⦆ _) M′—↠W′
            ++↠ ξ* (w′ ⦅ f ⦆[ □ ]) N′—↠ℰV′)
catchup-⟦perform⟧≤ v ([ ℰ ]⇑ g) (⇑≤⇑ .g M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ ¬e//ℰ
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ ([ ℰ≤ℰ′ ]⇑ g) ¬e//ℰ′
         (ξ* ([ □ ]⇑ g) M′—↠ℰV′)
catchup-⟦perform⟧≤ v (`cast ±p [ ℰ ])
                   (cast≤ comm M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ ¬e//ℰ
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ (cast≤ comm ℰ≤ℰ′) ¬e//ℰ′ M′—↠ℰV′
catchup-⟦perform⟧≤ v (″perform e∈E [ ℰ ] eq)
                     (perform≤perform M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ ¬e//ℰ
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ (″perform _ [ ℰ≤ℰ′ ] _) ¬e//ℰ′
         (ξ* (″perform _ [ □ ] _) M′—↠ℰV′)
catchup-⟦perform⟧≤ v (′handle H [ ℰ ])
       (handle≤handle {H′ = H′} H≤ M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ (¬e//ℰ ∘ inj₂)
... | Mk {ℰ′ = ℰ′} v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk  v′ V≤V′ (′handle H≤ [ ℰ≤ℰ′ ])
          (¬handled-handle {H = H′} ℰ′
            (subst (λ Eh → ¬ _ ∈ Eh)
                   (Hooks-≤ H≤)
                   (¬e//ℰ ∘ inj₁))
            ¬e//ℰ′)
          (ξ* (′handle _ [ □ ]) M′—↠ℰV′)
  where
    Hooks-≤ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᴳ Γ′}
                {P P′} {P≤ : P ≤ᶜ P′}
                {Q Q′} {Q≤ : Q ≤ᶜ Q′} {H H′}
      → Γ≤ ⊢ H ≤ H′ ⦂ P≤ ⇒ʰ Q≤
      → Hooks H ≡ Hooks H′
    Hooks-≤ H≤ = All₂′-≡ (on-perform H≤)
```
