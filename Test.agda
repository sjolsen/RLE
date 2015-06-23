module Test where
  open import Data.Nat
  open import Data.Vec
  open import Relation.Binary.PropositionalEquality
  open import Function
  open import RLE _≟_

  foo : Vec ℕ 6
  foo = 1 ∷ 1 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ []

  good : foo ≡ (decode ∘ encode $ foo)
  good = refl
