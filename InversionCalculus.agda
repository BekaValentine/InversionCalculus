open import Model

open import Category.Monad
open import Data.Empty
open import Data.List renaming (_∷_ to _∷List_)
open import Data.Maybe renaming (monadPlus to maybeMonadPlus)
open import Data.Nat hiding (_≟_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit hiding (_≟_)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module InversionCalculus {ℓ} (P : Set ℓ) (_≟P_ : (p p' : P) → Dec (p ≡ p')) (M : Model P) where

open Model.Model M

data Proposition : Set (lsuc ℓ) where
  atomic : P → Proposition
  T F : Proposition
  _∧_ _∨_ _⊃_ : Proposition → Proposition → Proposition

infixr 10 _∧_
infixr 9 _∨_
infixr 8 _⊃_

atomic-cong : ∀ {p p'} → atomic p ≡ atomic p' → p ≡ p'
atomic-cong refl = refl

∧-cong : ∀ {A B A' B'} → (A ∧ B) ≡ (A' ∧ B') → A ≡ A' × B ≡ B'
∧-cong refl = refl , refl

∨-cong : ∀ {A B A' B'} → (A ∨ B) ≡ (A' ∨ B') → A ≡ A' × B ≡ B'
∨-cong refl = refl , refl

⊃-cong : ∀ {A B A' B'} → (A ⊃ B) ≡ (A' ⊃ B') → A ≡ A' × B ≡ B'
⊃-cong refl = refl , refl

_≟_ : (A B : Proposition) → Dec (A ≡ B)
atomic p ≟ atomic p' with p ≟P p'
atomic p ≟ atomic .p | yes refl = yes refl
atomic p ≟ atomic p' | no ¬eq = no (λ eq → ¬eq (atomic-cong eq))
atomic p ≟ T = no (λ ())
atomic p ≟ F = no (λ ())
atomic p ≟ (B ∧ B₁) = no (λ ())
atomic p ≟ (B ∨ B₁) = no (λ ())
atomic p ≟ (B ⊃ B₁) = no (λ ())
T ≟ atomic x = no (λ ())
T ≟ T = yes refl
T ≟ F = no (λ ())
T ≟ (B ∧ B₁) = no (λ ())
T ≟ (B ∨ B₁) = no (λ ())
T ≟ (B ⊃ B₁) = no (λ ())
F ≟ atomic x = no (λ ())
F ≟ T = no (λ ())
F ≟ F = yes refl
F ≟ (B ∧ B₁) = no (λ ())
F ≟ (B ∨ B₁) = no (λ ())
F ≟ (B ⊃ B₁) = no (λ ())
(A ∧ A₁) ≟ atomic x = no (λ ())
(A ∧ A₁) ≟ T = no (λ ())
(A ∧ A₁) ≟ F = no (λ ())
(A ∧ A₁) ≟ (B ∧ B₁) with A ≟ B | A₁ ≟ B₁
(A ∧ A₁) ≟ (.A ∧ .A₁) | yes refl | yes refl = yes refl
... | no ¬eq | _       = no (λ eq → ¬eq (proj₁ (∧-cong eq)))
... | _      | no ¬eq' = no (λ eq → ¬eq' (proj₂ (∧-cong eq)))
(A ∧ A₁) ≟ (B ∨ B₁) = no (λ ())
(A ∧ A₁) ≟ (B ⊃ B₁) = no (λ ())
(A ∨ A₁) ≟ atomic x = no (λ ())
(A ∨ A₁) ≟ T = no (λ ())
(A ∨ A₁) ≟ F = no (λ ())
(A ∨ A₁) ≟ (B ∧ B₁) = no (λ ())
(A ∨ A₁) ≟ (B ∨ B₁) with A ≟ B | A₁ ≟ B₁
(A ∨ A₁) ≟ (.A ∨ .A₁) | yes refl | yes refl = yes refl
... | no ¬eq | _       = no (λ eq → ¬eq (proj₁ (∨-cong eq)))
... | _      | no ¬eq' = no (λ eq → ¬eq' (proj₂ (∨-cong eq)))
(A ∨ A₁) ≟ (B ⊃ B₁) = no (λ ())
(A ⊃ A₁) ≟ atomic x = no (λ ())
(A ⊃ A₁) ≟ T = no (λ ())
(A ⊃ A₁) ≟ F = no (λ ())
(A ⊃ A₁) ≟ (B ∧ B₁) = no (λ ())
(A ⊃ A₁) ≟ (B ∨ B₁) = no (λ ())
(A ⊃ A₁) ≟ (B ⊃ B₁) with A ≟ B | A₁ ≟ B₁
(A ⊃ A₁) ≟ (.A ⊃ .A₁) | yes refl | yes refl = yes refl
... | no ¬eq | _       = no (λ eq → ¬eq (proj₁ (⊃-cong eq)))
... | _      | no ¬eq' = no (λ eq → ¬eq' (proj₂ (⊃-cong eq)))

⟦_⟧ : Proposition → Set ℓ
⟦ atomic p ⟧ = I p
⟦ T        ⟧ = Lift ⊤
⟦ F        ⟧ = Lift ⊥
⟦ A ∧ B    ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A ∨ B    ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ A ⊃ B    ⟧ = ⟦ A ⟧ → ⟦ B ⟧

Negative : Proposition → Set
Negative (atomic _) = ⊤
Negative T = ⊤
Negative F = ⊥
Negative (A ∧ B) = ⊤
Negative (A ∨ B) = ⊥
Negative (A ⊃ B) = ⊤

Positive : Proposition → Set
Positive (atomic _) = ⊤
Positive T = ⊥
Positive F = ⊤
Positive (A ∧ B) = ⊥
Positive (A ∨ B) = ⊤
Positive (A ⊃ B) = ⊥

data Disjunction : Proposition → Set (lsuc ℓ) where
  yes : (A B : Proposition) → Disjunction (A ∨ B)

disjunction : (A : Proposition) → Dec (Disjunction A)
disjunction (atomic x) = no (λ ())
disjunction T = no (λ ())
disjunction F = no (λ ())
disjunction (A ∧ B) = no (λ ())
disjunction (A ∨ B) = yes (yes A B)
disjunction (A ⊃ B) = no (λ ())

record PosProp : Set (lsuc ℓ) where
  constructor _⁺
  field
    prop : Proposition
    {pos} : Positive prop

⟦_⟧⁺ : PosProp → Set _
⟦ A ⁺ ⟧⁺ = ⟦ A ⟧

infixl 7 _∷_

data Con : Set (lsuc ℓ) where
  [] : Con
  _∷_ : Con → Proposition → Con

data ⟦_⟧Con : Con → Set (lsuc ℓ) where
  [] : ⟦ [] ⟧Con
  _∷_ : ∀ {Γ A} → ⟦ Γ ⟧Con → ⟦ A ⟧ → ⟦ Γ ∷ A ⟧Con

data NegCon : Set (lsuc ℓ) where
  [] : NegCon
  _∷_ : NegCon → (A : Proposition) → {_ : Negative A} → NegCon

data ⟦_⟧NegCon : NegCon → Set (lsuc ℓ) where
  [] : ⟦ [] ⟧NegCon
  _∷_ : ∀ {Γ A} {negA : Negative A} → ⟦ Γ ⟧NegCon → ⟦ A ⟧ → ⟦ _∷_ Γ A {negA} ⟧NegCon

infix 6 _∋_
data _∋_ : NegCon → Proposition → Set (lsuc ℓ) where
  here : ∀ {Γ A} {negA : Negative A} →      _∷_ Γ A {negA} ∋ A
  there : ∀ {Γ A B} {negB : Negative B} →   Γ ∋ A   →   _∷_ Γ B {negB} ∋ A

mutual
  infix 5 _∣_—R⟶_
  infix 5 _∣_—L⟶_

  data _∣_—R⟶_ : NegCon → Con → Proposition → Set (lsuc ℓ) where
    
    -- inversion
    TR : ∀ {Γ Ω} →       Γ ∣ Ω —R⟶ T
    ∧R : ∀ {Γ Ω A B} →   Γ ∣ Ω —R⟶ A   →   Γ ∣ Ω —R⟶ B   →   Γ ∣ Ω —R⟶ A ∧ B
    ⊃R : ∀ {Γ Ω A B} →   Γ ∣ Ω ∷ A —R⟶ B   →   Γ ∣ Ω —R⟶ A ⊃ B
    init : ∀ {Γ Ω p} →   Γ ∋ atomic p   →   Γ ∣ Ω —R⟶ atomic p
    LRP : ∀ {Γ Ω p} →    ¬ Γ ∋ atomic p   →   Γ ∣ Ω —L⟶ atomic p ⁺   →   Γ ∣ Ω —R⟶ atomic p
    LR∨ : ∀ {Γ Ω A B} →   Γ ∣ Ω —L⟶ (A ∨ B) ⁺   →   Γ ∣ Ω —R⟶ A ∨ B
    LRF : ∀ {Γ Ω} →   Γ ∣ Ω —L⟶ F ⁺   →   Γ ∣ Ω —R⟶ F
  
  data _∣_—L⟶_ : NegCon → Con → PosProp → Set (lsuc ℓ) where
    
    -- inversion
    ∧L : ∀ {Γ Ω A B C} →   Γ ∣ Ω ∷ A ∷ B —L⟶ C   →   Γ ∣ Ω ∷ A ∧ B —L⟶ C
    TL : ∀ {Γ Ω C} →   Γ ∣ Ω —L⟶ C   →   Γ ∣ Ω ∷ T —L⟶ C
    ∨L : ∀ {Γ Ω A B C} →   Γ ∣ Ω ∷ A —L⟶ C   →   Γ ∣ Ω ∷ B —L⟶ C   →   Γ ∣ Ω ∷ A ∨ B —L⟶ C
    FL : ∀ {Γ Ω C} →   Γ ∣ Ω ∷ F —L⟶ C
    init : ∀ {Γ Ω p} →   Γ ∣ Ω ∷ atomic p —L⟶ atomic p ⁺
    shiftP : ∀ {Γ Ω p C} →   {¬eq : ¬ atomic p ⁺ ≡ C}   →   Γ ∷ atomic p ∣ Ω —L⟶ C   →   Γ ∣ Ω ∷ atomic p —L⟶ C
    shift⊃ : ∀ {Γ Ω A B C} →   Γ ∷ A ⊃ B ∣ Ω —L⟶ C   →   Γ ∣ Ω ∷ A ⊃ B —L⟶ C
    
    -- search
    ∨R₁ : ∀ {Γ A B} →   Γ ∣ [] —R⟶ A   →   Γ ∣ [] —L⟶ (A ∨ B) ⁺
    ∨R₂ : ∀ {Γ A B} →   Γ ∣ [] —R⟶ B   →   Γ ∣ [] —L⟶ (A ∨ B) ⁺
    ⊃L : ∀ {Γ A B C} →   Γ ∋ A ⊃ B   →   Γ ∣ [] —R⟶ A   →   Γ ∣ [] ∷ B —L⟶ C   →   Γ ∣ [] —L⟶ C

lookupNeg : {Γ : NegCon} {A : Proposition} → Γ ∋ A → ⟦ Γ ⟧NegCon → ⟦ A ⟧
lookupNeg here (G ∷ x) = x
lookupNeg (there v) (G ∷ x) = lookupNeg v G

mutual
  
  semR : ∀ {Γ Ω C} →   Γ ∣ Ω —R⟶ C   →   ⟦ Γ ⟧NegCon → ⟦ Ω ⟧Con → ⟦ C ⟧
  semR TR G O = lift tt
  semR (∧R x y) G O = semR x G O , semR y G O
  semR (⊃R x) G O = λ a → semR x G (O ∷ a)
  semR (init v) G O = lookupNeg v G
  semR (LRP neg x) G O = semL x G O
  semR (LR∨ x) G O = semL x G O
  semR (LRF x) G O = semL x G O
  
  semL : ∀ {Γ Ω C} →   Γ ∣ Ω —L⟶ C   →   ⟦ Γ ⟧NegCon → ⟦ Ω ⟧Con → ⟦ C ⟧⁺
  semL (∧L x) G (O ∷ (a , b)) = semL x G (O ∷ a ∷ b)
  semL (TL x) G (O ∷ lift tt) = semL x G O
  semL (∨L x y) G (O ∷ inj₁ l) = semL x G (O ∷ l)
  semL (∨L x y) G (O ∷ inj₂ r) = semL y G (O ∷ r)
  semL FL G (O ∷ lift ())
  semL init G (O ∷ p) = p
  semL (shiftP x) G (O ∷ p) = semL x (G ∷ p) O
  semL (shift⊃ x) G (O ∷ p) = semL x (G ∷ p) O
  semL (∨R₁ x) G O = inj₁ (semR x G O)
  semL (∨R₂ y) G O = inj₂ (semR y G O)
  semL (⊃L v x y) G O = semL y G (O ∷ lookupNeg v G (semR x G O))
