import InversionCalculus
open import Model

open import Category.Monad
open import Data.Empty
open import Data.List renaming (_∷_ to _∷List_)
open import Data.Nat hiding (_≟_)
open import Data.Maybe renaming (monadPlus to maybeMonadPlus)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit hiding (_≟_)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module InversionCalculusSolver {ℓ} (P : Set ℓ) (_≟P_ : (p p' : P) → Dec (p ≡ p')) (M : Model P) where

open InversionCalculus P _≟P_ M

open RawMonadPlus (maybeMonadPlus {f = (lsuc ℓ)})

∋-cong : ∀ Γ A {negA : Negative A} p → _∷_ Γ A {negA} ∋ atomic p → ¬ A ≡ atomic p → Γ ∋ atomic p
∋-cong Γ (atomic .p) p here ¬eq = ⊥-elim (¬eq refl)
∋-cong Γ (atomic x) p (there v) ¬eq = v
∋-cong Γ T p (there v) ¬eq = v
∋-cong Γ F {()} p v ¬eq
∋-cong Γ (A ∧ B) p (there v) ¬eq = v
∋-cong Γ (A ∨ B) {()} p v ¬eq
∋-cong Γ (A ⊃ B) p (there v) ¬eq = v

findNegCon : ∀ Γ p → Dec (Γ ∋ atomic p)
findNegCon [] p = no (λ ())
findNegCon (Γ ∷ atomic p') p with p' ≟P p
findNegCon (Γ ∷ atomic .p) p | yes refl = yes here
... | no ¬eq with findNegCon Γ p
... | yes mem = yes (there mem)
... | no ¬mem = no (λ x → ¬mem (∋-cong Γ (atomic p') p x (λ y → ¬eq (atomic-cong y))))
findNegCon (_∷_ Γ T {tt}) p with findNegCon Γ p
... | yes mem = yes (there mem)
... | no ¬mem = no (λ x → ¬mem (∋-cong Γ T p x (λ ())))
findNegCon (_∷_ Γ F {()}) p
findNegCon (_∷_ Γ (A ∧ B) {tt}) p with findNegCon Γ p
... | yes mem = yes (there mem)
... | no ¬mem = no (λ x → ¬mem (∋-cong Γ (A ∧ B) p x (λ ())))
findNegCon (_∷_ Γ (A ∨ B) {()}) p
findNegCon (_∷_ Γ (A ⊃ B) {tt}) p with findNegCon Γ p
... | yes mem = yes (there mem)
... | no ¬mem = no (λ x → ¬mem (∋-cong Γ (A ⊃ B) p x (λ ())))

findImplications : ∀ Γ → List (Σ[ A ∶ Proposition ] Σ[ B ∶ Proposition ] Γ ∋ A ⊃ B)
findImplications [] = []
findImplications (Γ ∷ A ⊃ B) = (A , B , here) ∷List map (λ { (B , C , v) → B , C , there v }) (findImplications Γ)
findImplications (Γ ∷ A)     = map (λ { (B , C , v) → B , C , there v }) (findImplications Γ)

mutual
  invertR : ∀ (n : ℕ) Γ Ω A → Maybe (Γ ∣ Ω —R⟶ A)
  invertR 0       Γ Ω A = nothing
  invertR (suc n) Γ Ω (atomic p) with findNegCon Γ p
  ... | yes mem = just (init mem)
  ... | no ¬mem = invertL n Γ Ω (atomic p ⁺) >>= λ x →
                  just (LRP ¬mem x)
  invertR (suc n) Γ Ω T = just TR
  invertR (suc n) Γ Ω F = nothing
  invertR (suc n) Γ Ω (A ∧ B) = invertR n Γ Ω A >>= λ x →
                                invertR n Γ Ω B >>= λ y →
                                just (∧R x y)
  invertR (suc n) Γ Ω (A ∨ B) = invertL n Γ Ω ((A ∨ B) ⁺) >>= λ x →
                                just (LR∨ x)
  invertR (suc n) Γ Ω (A ⊃ B) = invertR n Γ (Ω ∷ A) B >>= λ x →
                                just (⊃R x)
  
  invertL : ∀ (n : ℕ) Γ Ω C → Maybe (Γ ∣ Ω —L⟶ C)
  invertL 0 Γ Ω C = nothing
  invertL (suc n) Γ [] C = search n Γ C
  invertL (suc n) Γ (Ω ∷ atomic p) (_⁺ C {pos}) with C ≟ atomic p
  ... | yes eq rewrite eq = just init
  ... | no ¬eq = invertL n (Γ ∷ atomic p) Ω (_⁺ C {pos}) >>= λ x →
                 just (shiftP {¬eq = λ eq⁺ → ¬eq (sym (cong PosProp.prop eq⁺))} x)
  invertL (suc n) Γ (Ω ∷ T) C = invertL n Γ Ω C >>= λ x →
                                just (TL x)
  invertL (suc n)  Γ (Ω ∷ F) C = just FL
  invertL (suc n)  Γ (Ω ∷ A ∧ B) C = invertL n Γ (Ω ∷ A ∷ B) C >>= λ x →
                                     just (∧L x)
  invertL (suc n) Γ (Ω ∷ A ∨ B) C = invertL n Γ (Ω ∷ A) C >>= λ x →
                                    invertL n Γ (Ω ∷ B) C >>= λ y →
                                    just (∨L x y)
  invertL (suc n) Γ (Ω ∷ A ⊃ B) C = invertL n (Γ ∷ A ⊃ B) Ω C >>= λ x →
                                    just (shift⊃ x)
  
  search∨ : ∀ (n : ℕ) Γ C → Maybe (Γ ∣ [] —L⟶ C)
  search∨ 0 Γ C = nothing
  search∨ (suc n) Γ (C ⁺) with disjunction C
  search∨ (suc n) Γ (.(A ∨ B) ⁺) | yes (yes A B) with invertR n Γ [] A
  ... | just x = just (∨R₁ x)
  ... | nothing with invertR n Γ [] B
  ... | just y = just (∨R₂ y)
  ... | nothing = nothing
  search∨ (suc n) Γ (C ⁺) | no _ = nothing
  
  search⊃ : ∀ (n : ℕ) Γ C → Maybe (Γ ∣ [] —L⟶ C)
  search⊃ 0 Γ C = nothing
  search⊃ (suc n) Γ C = go (findImplications Γ)
    where go : List (Σ[ A ∶ Proposition ] Σ[ B ∶ Proposition ] Γ ∋ A ⊃ B) → Maybe (Γ ∣ [] —L⟶ C)
          go [] = nothing
          go ((A , B , v) ∷List imps) with invertR n Γ [] A >>= λ x →
                                           invertL n Γ ([] ∷ B) C >>= λ y →
                                           just (⊃L v x y)
          ... | just x = just x
          ... | nothing = go imps
  
  search : ∀ (n : ℕ) Γ C → Maybe (Γ ∣ [] —L⟶ C)
  search 0 Γ C = nothing
  search (suc n) Γ C with search∨ n Γ C
  ... | just x = just x
  ... | nothing = search⊃ n Γ C

prove : ∀ (n : ℕ) {Ω : Con} A → Maybe (⟦ Ω ⟧Con → ⟦ A ⟧)
prove n {Ω} A with invertR n [] Ω A
... | just x = just (semR x [])
... | nothing = nothing

prove′ : ∀ (n : ℕ) A → Maybe ⟦ A ⟧
prove′ n A with invertR n [] [] A
... | just x = just (semR x [] [])
... | nothing = nothing
