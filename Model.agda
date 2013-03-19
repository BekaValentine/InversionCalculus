open import Level

module Model where

record Model {ℓ} (P : Set ℓ) : Set (suc ℓ) where
  field
    I : P → Set ℓ
