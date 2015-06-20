module Nat-aux where
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality

  suc-inj : ∀ {m n} → ℕ.suc m ≡ ℕ.suc n → m ≡ n
  suc-inj refl = refl

  +→≤′-lemmaʳ : ∀ a b m → a + b ≡ m → b ≤′ m
  +→≤′-lemmaʳ zero     _ _        x = subst₂ _≤′_ refl x ≤′-refl
  +→≤′-lemmaʳ (suc a′) _ zero     ()
  +→≤′-lemmaʳ (suc a′) b (suc m′) x = ≤′-step (+→≤′-lemmaʳ a′ b m′ (suc-inj x))

  s≤′s : ∀ a b → a ≤′ b → suc a ≤′ suc b
  s≤′s a .a       ≤′-refl     = ≤′-refl
  s≤′s a (suc b′) (≤′-step x) = ≤′-step (s≤′s a b′ x)

  s⁻¹≤′s⁻¹ : ∀ a b → suc a ≤′ suc b → a ≤′ b
  s⁻¹≤′s⁻¹ a .a       ≤′-refl     = ≤′-refl
  s⁻¹≤′s⁻¹ a zero     (≤′-step ())
  s⁻¹≤′s⁻¹ a (suc b′) (≤′-step x) = ≤′-step (s⁻¹≤′s⁻¹ a b′ x)
