module Nat-aux where
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality

  suc-inj : ∀ {m n} → ℕ.suc m ≡ ℕ.suc n → m ≡ n
  suc-inj refl = refl

  <′-lemma : ∀ a b n → suc a + b ≡ n → b <′ n
  <′-lemma zero     b n        x = subst₂ _≤′_ refl x ≤′-refl
  <′-lemma (suc a′) b zero     ()
  <′-lemma (suc a′) b (suc n′) x = ≤′-step (<′-lemma a′ b n′ (suc-inj x))
