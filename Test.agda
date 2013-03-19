import InversionCalculus
import InversionCalculusSolver
open import Model

open import Data.Maybe
open import Data.Nat hiding (_≟_)
open import Data.Product hiding (swap)
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module Test where

postulate A B C : Set

data U : Set where
  UA UB UC : U

_≟_ : (u u' : U) → Dec (u ≡ u')
UA ≟ UA = yes refl
UA ≟ UB = no (λ ())
UA ≟ UC = no (λ ())
UB ≟ UA = no (λ ())
UB ≟ UB = yes refl
UB ≟ UC = no (λ ())
UC ≟ UA = no (λ ())
UC ≟ UB = no (λ ())
UC ≟ UC = yes refl

UModel : Model U
UModel = record { I = λ { UA → A
                        ; UB → B
                        ; UC → C
                        }
                }

open InversionCalculus U _≟_ UModel hiding (_≟_) renaming (atomic to [_])
open InversionCalculusSolver U _≟_ UModel

[A] : Proposition
[A] = [ UA ]

[B] : Proposition
[B] = [ UB ]

[C] : Proposition
[C] = [ UC ]

I : A → A
I = from-just (prove′ 3 ([A] ⊃ [A]))

K : A → B → A
K = from-just $ prove′ 5 $  [A] ⊃ [B] ⊃ [A]

swap : A × B → B × A
swap = from-just $ prove′ 6 $  [A] ∧ [B]  ⊃  [B] ∧ [A]

compose : (A → B) → (B → C) → (A → C)
compose = from-just $ prove′ 15 $  ([A] ⊃ [B])  ⊃  ([B] ⊃ [C])  ⊃  ([A] ⊃ [C])

S : (A → B → C) → (A → B) → (A → C)
S = from-just $ prove′ 19 $  ([A] ⊃ [B] ⊃ [C])  ⊃  ([A] ⊃ [B])  ⊃  ([A] ⊃ [C])
