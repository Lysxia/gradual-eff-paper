## Proof of the Gradual Guarantee

```
{-# OPTIONS --allow-unsolved-metas #-} -- TODO
module SimAux where

open import Utils
open import Type
open import Core
open import Progress
open import Prec
```

```
gvalue≤gvalue : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᴳ Γ′} {A A′} {A≤ : A ≤ A′} {E E′} {E≤ : E ≤ᵉ E′} {V : Γ ⊢ ⟨ E ⟩ A} {V′ : Γ′ ⊢ ⟨ E′ ⟩ A′}
  → (v  : Value V)
  → (v′ : Value V′)
  → Γ≤ ⊢ V ≤ᴹ V′ ⦂ ⟨ E≤ ⟩ A≤
  → ∀ {F F′} {F≤ : F ≤ᵉ F′}
  → Γ≤ ⊢ gvalue v ≤ᴹ gvalue v′ ⦂ ⟨ F≤ ⟩ A≤
gvalue≤gvalue ($ _) ($ _) ($≤$ κ) = $≤$ κ
gvalue≤gvalue (v ⇑ _) (v′ ⇑ _) (⇑≤⇑ g V≤) = ⇑≤⇑ g (gvalue≤gvalue v v′ V≤)
gvalue≤gvalue v (v′ ⇑ _) (≤⇑ g V≤) = ≤⇑ g (gvalue≤gvalue v v′ V≤)
gvalue≤gvalue (ƛ _) (ƛ _) (ƛ≤ƛ N≤N′) = ƛ≤ƛ N≤N′
gvalue≤gvalue (ƛ _) (ƛ _) (wrap≤ i e ƛN≤ƛN′) = wrap≤ i e ƛN≤ƛN′
gvalue≤gvalue (ƛ _) (ƛ _) (≤wrap i e ƛN≤ƛN′) = ≤wrap i e ƛN≤ƛN′

gValue : ∀ {Γ E A} {V : Γ ⊢ ⟨ E ⟩ A} → (v : Value V) → ∀ {F} → Value (gvalue v {F = F})
gValue (ƛ N) = ƛ N
gValue ($ κ) = $ κ
gValue (v ⇑ g) = gValue v ⇑ g

≤gvalue : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᴳ Γ′} {A A′} {A≤ : A ≤ A′} {E E′} {E≤ : E ≤ᵉ E′} {V : Γ ⊢ ⟨ E ⟩ A} {V′ : Γ′ ⊢ ⟨ E′ ⟩ A′}
  → (v  : Value V)
  → (v′ : Value V′)
  → Γ≤ ⊢ V ≤ᴹ V′ ⦂ ⟨ E≤ ⟩ A≤
  → ∀ {F′} {F≤ : E ≤ᵉ F′}
  → Γ≤ ⊢ V ≤ᴹ gvalue v′ ⦂ ⟨ F≤ ⟩ A≤
≤gvalue ($ _) ($ _) ($≤$ κ) = $≤$ κ
≤gvalue (v ⇑ _) (v′ ⇑ _) (⇑≤⇑ g V≤) = ⇑≤⇑ g (≤gvalue v v′ V≤)
≤gvalue v (v′ ⇑ _) (≤⇑ g V≤) = ≤⇑ g (≤gvalue v v′ V≤)
≤gvalue (ƛ _) (ƛ _) (ƛ≤ƛ N≤N′) = ƛ≤ƛ N≤N′
≤gvalue (ƛ _) (ƛ _) (wrap≤ i e ƛN≤ƛN′) = wrap≤ i e ƛN≤ƛN′
≤gvalue (ƛ _) (ƛ _) (≤wrap i e ƛN≤ƛN′) = ≤wrap i e ƛN≤ƛN′

gvalue≤ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᴳ Γ′} {A A′} {A≤ : A ≤ A′} {E E′} {E≤ : E ≤ᵉ E′} {V : Γ ⊢ ⟨ E ⟩ A} {V′ : Γ′ ⊢ ⟨ E′ ⟩ A′}
  → (v : Value V)
  → (v′ : Value V′)
  → Γ≤ ⊢ V ≤ᴹ V′ ⦂ ⟨ E≤ ⟩ A≤
  → ∀ {F} {F≤ : F ≤ᵉ E′}
  → Γ≤ ⊢ gvalue v ≤ᴹ V′ ⦂ ⟨ F≤ ⟩ A≤
gvalue≤ ($ _) ($ _) ($≤$ κ) = $≤$ κ
gvalue≤ (v ⇑ _) (v′ ⇑ _) (⇑≤⇑ g V≤) = ⇑≤⇑ g (gvalue≤ v v′ V≤)
gvalue≤ v (v′ ⇑ _) (≤⇑ g V≤) = ≤⇑ g (gvalue≤ v v′ V≤)
gvalue≤ (ƛ _) (ƛ _) (ƛ≤ƛ N≤N′) = ƛ≤ƛ N≤N′
gvalue≤ (ƛ _) (ƛ _) (wrap≤ i e ƛN≤ƛN′) = wrap≤ i e ƛN≤ƛN′
gvalue≤ (ƛ _) (ƛ _) (≤wrap i e ƛN≤ƛN′) = ≤wrap i e ƛN≤ƛN′
```

## Cast lemma
```
cast-lemma : ∀ {Γ Γ′ A B C} {Γ≤ : Γ ≤ᴳ Γ′} {p : A ≤ᶜ B} {r : A ≤ᶜ C}
           {V : Γ ⊢ A} {V′ : Γ′ ⊢ B}
  → Value V
  → Value V′
  → (±q : B =>ᶜ C)
  → ≤commuteᶜ p ±q r
  → Γ≤ ⊢ V ≤ᴹ V′ ⦂ p
    -------------------------------------------------------
  → ∃[ W ] (Value W × (cast ±q V′ —↠ W) × (Γ≤ ⊢ V ≤ᴹ W ⦂ r))
cast-lemma v v′ ±q e V≤V′ with splitᶜ ±q in e′
cast-lemma v v′ ±q e V≤V′ | id = ? -- TODO
{-
    rewrite ≤ident ±q e′ e
    =  _ , v′ , unit (ident e′ v′) , V≤V′
-}
cast-lemma (ƛ _) (ƛ _) ±q e ƛN≤ƛN′ | ∓s ⇒ ±t
    =  ƛ _ , ƛ _ , unit (wrap e′) , ≤wrap e′ {! e !} (generalize-ƛ≤ƛ ƛN≤ƛN′)
cast-lemma v v′ (+ ⟨ E≤E′ ⟩ (q ⇑ g)) refl V≤V′ | other
    with cast-lemma v v′ (+ ⟨ E≤E′ ⟩ q) refl V≤V′
... |  W′ , w , V′+—↠W′ , V≤W′
    =  (W′ ⇑ g) , (w ⇑ g) , (unit (expand v′ g) ++↠ ξ* ([ □ ]⇑ g) V′+—↠W′) , ≤⇑ g V≤W′
cast-lemma v (v′ ⇑ g) (- ⟨ E′≤E ⟩ (q ⇑ .g)) refl (≤⇑ .g  V≤V′) | other
    with cast-lemma v v′ (- ⟨ E′≤E ⟩ q) refl V≤V′
... |  W′ , w′ , V′-—↠W′ , V≤W′
    =  W′ , w′ , (unit (collapse v′ g) ++↠ V′-—↠W′) , V≤W′
```

## Catch up lemma

Catch up Lemma.  If `V ≤ᴹ M′` then `M′ —↠ V′` and `V ≤ᴹ V′` for some `V′`.
```
catchup : ∀ {Γ Γ′ A A′} {Γ≤ : Γ ≤ᴳ Γ′} {p : A ≤ᶜ A′} {V : Γ ⊢ A} {M′ : Γ′ ⊢ A′}
  → Value V
  → Γ≤ ⊢ V ≤ᴹ M′ ⦂ p
    ----------------------------------------------------
  → ∃[ V′ ](Value V′ × (M′ —↠ V′) × (Γ≤ ⊢ V ≤ᴹ V′ ⦂ p))
catchup (ƛ _) (ƛ≤ƛ {N′ = N′} ƛN≤ƛN′)
    =  ƛ N′ , ƛ N′ , (ƛ N′ ∎) , ƛ≤ƛ ƛN≤ƛN′
catchup ($ _) ($≤$ k)
    =  $ k , $ k , ($ k ∎) , ($≤$ k)
catchup (v ⇑ g) (⇑≤⇑ {M = V} {M′ = M′} .g V≤M′)
    with catchup v V≤M′
... |  V′ , v′ , M′—↠V′ , V≤V′
    =  V′ ⇑ g , v′ ⇑ g , ξ* ([ □ ]⇑ g) M′—↠V′ , ⇑≤⇑ g V≤V′
catchup v (≤⇑ h V≤M′)
    with catchup v V≤M′
... |  V′ , v′ , M′—↠V′ , V≤V′
    =  V′ ⇑ h , v′ ⇑ h , ξ* ([ □ ]⇑ h) M′—↠V′ , ≤⇑ h V≤V′
catchup v (≤cast {M′ = M′} {±q = ±q} e V≤M′)
    with catchup v V≤M′
... |  V′ , v′ , M′—↠V′ , V≤V′
    with cast-lemma v v′ ±q e V≤V′
... |  W , w , V⟨±q⟩—↠W , V≤W
    =  W , w , (ξ* (`cast ±q [ □ ]) M′—↠V′ ++↠ V⟨±q⟩—↠W) , V≤W
catchup (ƛ _) (wrap≤ e′ e ƛN≤ƛN′)
    =  _ , ƛ _ , (_ ∎) , wrap≤ e′ e ƛN≤ƛN′
catchup (ƛ _) (≤wrap e′ e ƛN≤ƛN′)
    =  _ , ƛ _ , (_ ∎) , ≤wrap e′ e ƛN≤ƛN′
```

## Substitution lemma

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
  σId : ∀ {A} {E : Effs} (x : Γ ∋ A) → _≡_ {A = _ ⊢ ⟨ _ ⟩ _} (`_ {E = E} x) (` x)  -- TODO what's going on with inference here
  σId x = refl
```

The following lemma describes β-reduction of a wrap applied to a
value, using the lemma above to simplify the right-hand side of the
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

```
simβ : ∀ {Γ Γ′ A A′ B B′ E E′} {Γ≤ : Γ ≤ᴳ Γ′} {p : A ⇒  ⟨ E ⟩ B ≤ A′ ⇒  ⟨ E′ ⟩ B′} {E≤ : E ≤ᵉ E′}
    {N : Γ ▷ A ⊢ ⟨ E ⟩ B} {N′ : Γ′ ▷ A′ ⊢ ⟨ E′ ⟩ B′} {W : Γ ⊢ ⟨ E ⟩ A} {W′ : Γ′ ⊢ ⟨ E′ ⟩ A′}
  → (w  : Value W)
  → (w′ : Value W′)
  → Γ≤ ⊢ ƛ N ≤ᴹ ƛ N′ ⦂ ⟨ E≤ ⟩ p
  → Γ≤ ⊢ W ≤ᴹ W′ ⦂ ⟨ E≤ ⟩ dom p
    -----------------------------------------------------------
  → ∃[ M′ ](((ƛ N′) · W′ —↠ M′) × (Γ≤ ⊢ N [ gvalue w ] ≤ᴹ M′ ⦂ cod p))

simβ w w′ (ƛ≤ƛ N≤N′) W≤W′
    =  _ , (unit (β w′)) , ([]≤[] N≤N′ (gvalue≤gvalue w w′ W≤W′))

simβ {W = W}{W′} w w′ (wrap≤ {B = ⟨ E ⟩ _} {N = N}{N′}{r = r} e′ e ƛN≤ƛN′) W≤W′
    rewrite lift[] {P = ⟨ E ⟩ _} (ƛ N) (gvalue w)
    =  (ƛ N′) · W′ , (_ ∎) , cast≤ (cod≤ e′ e) (·≤· ƛN≤ƛN′ (cast≤ {r = ⟨ _≤ᶜ_.effects (cod r) ⟩ _} (pure≤ {q = ⟨ id ⟩ _} {r = ⟨ id ⟩ _} (dom≤ e′ e)) (gvalue≤ w w′ W≤W′)))
  where qq = (cod≤ e′ e)

simβ {W = W}{W′} w w′ (≤wrap {B′ = ⟨ E′ ⟩ _} {N = N}{N′}{p = p}{r = r}{∓s = ∓s}{±t = ±t} e′ e ƛN≤ƛN′) W≤W′
  = ?
{-
    with cast-lemma w (gValue w′) (pure± ∓s) (≤pure {p = ⟨ _≤ᶜ_.effects (cod r) ⟩ _} {r = ⟨ ? ⟩ _} (≤dom e′ e)) (≤gvalue w w′ W≤W′)
      where F≤ = let ⟨ F≤ ⟩ _ = cod p in F≤
... |  W″ , w″ , W′-—↠W″ , W≤W″
    with simβ w w″ ƛN≤ƛN′ W≤W″
... |  M′ , [ƛN′]·W″—↠M′ , N[W]≤M′
    =  cast ±t M′ ,
       (  begin
            ƛ-wrap ∓s ±t (ƛ N′) · W′
          —→⟨ wrapβ {V = ƛ N′} e′ w′ ⟩
            cast ±t ((ƛ N′) · cast (pure± ∓s) (gvalue w′))
          —↠⟨ ξ* (`cast _ [ (ƛ _) ·[ □ ] ]) W′-—↠W″ ⟩
            cast ±t ((ƛ N′) · W″)
          —↠⟨ ξ* (`cast _ [ □ ]) [ƛN′]·W″—↠M′ ⟩
            cast ±t M′
          ∎) ,
       (≤cast (≤cod e′ e) N[W]≤M′)
-}
```   

```
Hooks-≤ : ∀ {Γ Γ′} {Γ≤ : Γ ≤ᴳ Γ′} {P P′} {P≤ : P ≤ᶜ P′} {Q Q′} {Q≤ : Q ≤ᶜ Q′} {H H′}
  → Γ≤ ⊢ H ≤ H′ ⦂ P≤ ➡ Q≤
  → Hooks H ≡ Hooks H′
Hooks-≤ H≤ = All₂′-≡ (on-perform H≤)

data CatchupPerform {Γ Γ′} (Γ≤ : Γ ≤ᴳ Γ′) {P P′} (P≤ : P ≤ᶜ P′) {E} e (ℰ : Frame Γ (⟨ E ⟩ response e) P) (V : Γ ⊢ ⟨ E ⟩ request e) (M′ : Γ′ ⊢ P′) : Set where
  Mk : ∀ {E′} {E≤ : E ≤ᵉ E′} {e∈E′ : e ∈☆ E′} {V′}
         {ℰ′ : Frame Γ′ (⟨ E′ ⟩ response e) P′}
    → Value V′
    → Γ≤ ⊢ V ≤ᴹ V′ ⦂ ⟨ E≤ ⟩ id
    → Γ≤ ⊢ ⟨ E≤ ⟩ id ⇒ᶠ P≤ ∋ ℰ ≤ ℰ′
    → ¬ handled e ℰ′
    → M′ —↠ ℰ′ ⟦ perform e∈E′ V′ ⟧
    → CatchupPerform Γ≤ P≤ e ℰ V M′

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
{-
catchup-⟦perform⟧≤ {e∈E = e∈E} v ℰ (≤⟨⟩ {E≤ = E≤} {±p = ±p} M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ ¬e//ℰ
... | Mk {ℰ′ = ℰ′} v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ (≤⟨⟩ ℰ≤ℰ′) (¬handled-cast⟨⟩ {±p = ±p} ℰ′ (∈-≤ E≤ (¬handled-∈ ℰ ¬e//ℰ e∈E)) ¬e//ℰ′) (ξ* ([ □ ]cast⟨ _ ⟩) M′—↠ℰV′)
-}
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
catchup-⟦perform⟧≤ v (″perform e∈E [ ℰ ] eq) (perform≤perform M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ ¬e//ℰ
... | Mk v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ (″perform _ [ ℰ≤ℰ′ ] _) ¬e//ℰ′ (ξ* (″perform _ [ □ ] _) M′—↠ℰV′)
catchup-⟦perform⟧≤ v (′handle H [ ℰ ]) (handle≤handle {H′ = H′} H≤ M≤) ¬e//ℰ
  with catchup-⟦perform⟧≤ v ℰ M≤ (¬e//ℰ ∘ inj₂)
... | Mk {ℰ′ = ℰ′} v′ V≤V′ ℰ≤ℰ′ ¬e//ℰ′ M′—↠ℰV′
    = Mk v′ V≤V′ (′handle H≤ [ ℰ≤ℰ′ ]) (¬handled-handle {H = H′} ℰ′ (subst (λ Eh → ¬ _ ∈ Eh) (Hooks-≤ H≤) (¬e//ℰ ∘ inj₁)) ¬e//ℰ′) (ξ* (′handle _ [ □ ]) M′—↠ℰV′)
```
