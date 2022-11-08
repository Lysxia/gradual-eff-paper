```
module Utils where

open import Function.Base using (_∘_; flip) public
open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Unit.Base using (⊤; tt) public
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (≡-isDecEquivalence)
open import Data.Nat.Base using (ℕ; zero; suc; _+_) public
import Data.Nat.Properties as Nat
open import Data.List.Base as List using (List; []; _∷_; _++_) public
open import Data.List.Membership.Propositional as List using (_∈_) public
open import Data.List.Relation.Unary.All as All using (All; []; _∷_) public
open import Data.List.Relation.Unary.Any as Any using (here; there) public
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_) public
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl) public
import Data.List.Relation.Binary.Equality.DecPropositional as List using (_≡?_)
import Data.List.Membership.DecPropositional as List using (_∈?_)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as VecPw using (Pointwise; []; _∷_)
import Data.Vec.Relation.Binary.Equality.DecPropositional as Vec
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax) public
open import Data.String as String using (String) public
open import Data.Sum using (_⊎_; inj₁; inj₂) public
open import Relation.Nullary using (¬_; Dec; yes; no) public
open import Relation.Nullary.Decidable using (_×-dec_) public
open import Relation.Nullary.Decidable.Core using (map′)
open import Relation.Binary using (REL; Rel; Decidable) public
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; cong₂; subst) public
open import Relation.Binary.Structures using () renaming (IsDecEquivalence to IDE)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (Star; _◅_; _◅◅_) renaming (ε to refl)

record DecEq {l} (A : Set l) : Set l where
  field _≟_ : Decidable (_≡_ {A = A})

open DecEq ⦃...⦄ public

instance
  DecEq-String : DecEq String
  DecEq-String = record { _≟_ = String._≟_ }

  DecEq-ℕ : DecEq ℕ
  DecEq-ℕ = record { _≟_ = Nat._≟_ }

  DecEq-⊥ : DecEq ⊥
  DecEq-⊥ = record { _≟_ = λ() }

  DecEq-Fin : {n : ℕ} → DecEq (Fin n)
  DecEq-Fin = record { _≟_ = IDE._≟_ ≡-isDecEquivalence }

  DecEq-List : ∀ {A : Set} ⦃ _ : DecEq A ⦄ → DecEq (List A)
  DecEq-List = record { _≟_ = List._≡?_ _≟_ }

  DecEq-Vec : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {n : ℕ} → DecEq (Vec A n)
  DecEq-Vec {A} = record { _≟_ = _≡?_ }
    where
      infix 4 _≡?_
      _≡?_ : ∀ {n} → Decidable {A = Vec A n} _≡_
      [] ≡? [] = yes refl
      x ∷ xs ≡? y ∷ ys with x ≟ y ×-dec xs ≡? ys
      ... | yes (refl , refl) = yes refl
      ... | no ¬≡ = no λ{ refl → ¬≡ (refl , refl) }

_∈?_ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ → Decidable {A = A} _∈_
_∈?_ = List._∈?_ _≟_

_⊆?_ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ → Decidable {A = List A} _⊆_
[] ⊆? F = yes λ()
(e ∷ E) ⊆? F with e ∈? F ×-dec E ⊆? F
... | yes (e∈F , E⊆F) = yes λ{ (here refl) → e∈F ; (there e∈E) → E⊆F e∈E }
... | no ¬∈×⊆ = no λ{ e∷E⊆F → ¬∈×⊆ (e∷E⊆F (here refl), λ{ e∈E → e∷E⊆F (there e∈E) }) }

singleton-∈-⊆ : ∀ {A : Set} {e : A} {E} → e ∈ E → (e ∷ []) ⊆ E
singleton-∈-⊆ e∈E (here refl) = e∈E

infix 0 _yes→_no→_
_yes→_no→_ : ∀ {A B : Set} → Dec A → (A → B) → (B → A) → Dec B
yes a yes→ A→ no→ A← = yes (A→ a)
no ¬A yes→ A→ no→ A← = no (¬A ∘ A←)

_Reflects_⟵_ : ∀ {ℓ} {A B : Set} → (A → B) → Rel A ℓ → Rel B ℓ → Set ℓ
f Reflects _<ᴬ_ ⟵ _<ᴮ_ = ∀ {x x′} → f x <ᴮ f x′ → x <ᴬ x′

_Reflects₂_×_⟵_ : ∀ {ℓ} {A B C : Set} → (A → B → C) → Rel A ℓ → Rel B ℓ → Rel C ℓ → Set ℓ
_∙_ Reflects₂ _<₁_ × _<₂_ ⟵ _<_ = ∀ {x x′ y y′} → (x ∙ y) < (x′ ∙ y′) → (x <₁ x′) × (y <₂ y′)

flip-VecPw : ∀ {ℓ} {A B : Set} {_≈_ : REL A B ℓ} {n} {xs ys}
  → Pointwise (flip _≈_) {n = n} ys xs → Pointwise _≈_ {n = n} xs ys
flip-VecPw [] = []
flip-VecPw (R ∷ Rs) = R ∷ flip-VecPw Rs

map-⊆ : ∀ {ℂ : Set} {Cs Ds : List ℂ} → Cs ⊆ Ds → ∀ {A : Set} → Vec A (List.length Ds) → Vec A (List.length Cs)
map-⊆ {Cs = []} _ _ = []
map-⊆ {Cs = C ∷ Cs} Cs⊆Ds Bs = Vec.lookup Bs (Any.index (Cs⊆Ds (here refl))) ∷ map-⊆ (Cs⊆Ds ∘ there) Bs

map-⊆-refl : ∀ {ℂ : Set} {Cs : List ℂ} {A : Set} {As : Vec A (List.length Cs)} → map-⊆ ⊆-refl As ≡ As
map-⊆-refl {Cs = Ds} {As = Bs} = aux ⊆-refl (λ _ → refl)
  where
    aux : ∀ {Cs} (Cs⊆Ds : Cs ⊆ Ds) {As : Vec _ (List.length Cs)} →
      (∀ {C} (i : C ∈ Cs) → Vec.lookup Bs (Any.index (Cs⊆Ds i)) ≡ Vec.lookup As (Any.index i)) →
      map-⊆ Cs⊆Ds Bs ≡ As
    aux {Cs = []} _ {[]} _ = refl
    aux {Cs = C ∷ Cs} Cs⊆Ds {A ∷ As} f = cong₂ _∷_ (f (here refl)) (aux {Cs = Cs} (Cs⊆Ds ∘ there) (f ∘ there))

Star-snoc : ∀ {ℓ ℓ₁} {I : Set ℓ} {T : Rel I ℓ₁} → ∀ {x y z} → Star T x y → T y z -> Star T x z
Star-snoc steps step = steps ◅◅ Star.return step
```
