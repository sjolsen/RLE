module NatPlus where
  open import Data.Nat
  open import Relation.Nullary.Decidable

  Nonzero : ℕ → Set
  Nonzero n = False (n ≟ 0)

  data ℕ⁺ : Set where
    +_ : ∀ (n : ℕ) {p : Nonzero n} → ℕ⁺

  toℕ : ℕ⁺ → ℕ
  toℕ (+ n) = n

  suc⁺ : ℕ⁺ → ℕ⁺
  suc⁺ n = + suc (toℕ n)
