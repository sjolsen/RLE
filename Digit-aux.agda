module Digit-aux where
  open import Data.Digit
  open import Data.Fin as Fin
  open import Data.Nat hiding (_≟_)
  open import Function.Injection
  open import Nat-aux
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality as PropEq

  toℕ-inj : ∀ {b} (x y : Fin b) → toℕ x ≡ toℕ y → x ≡ y
  toℕ-inj zero    zero    _  = refl
  toℕ-inj zero    (suc _) ()
  toℕ-inj (suc _) zero    ()
  toℕ-inj (suc x) (suc y) z  = PropEq.cong suc (toℕ-inj x y (suc-inj z))

  _≟_ : ∀ {b} → Decidable {A = Digit b} _≡_
  _≟_ = eq?
    record {
      to = record {
        _⟨$⟩_ = toℕ ;
        cong  = PropEq.cong toℕ
      } ;
      injective = λ {x} {y} z → toℕ-inj x y z
    }
