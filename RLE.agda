open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module RLE {ℓ} {X : Set ℓ} (_X-≟_ : Decidable {A = X} _≡_) where
  open import Data.Nat
  open import Data.Product
  open import Data.Vec hiding ([_]; head)
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Function
  open import NatPlus

  mutual
    infixr 5 _∷_ ↑_

    data RLE-Seq⁺ : ℕ⁺ → Set ℓ where
      [_] : ∀ (x : X)                                        → RLE-Seq⁺ (+ 1)
      _∷_ : ∀ (x : X) {n} (xs : RLE-Seq⁺ n) {alt : Alt x xs} → RLE-Seq⁺ (suc⁺ n)
      ↑_  : ∀         {n} (xs : RLE-Seq⁺ n)                  → RLE-Seq⁺ (suc⁺ n)

    Alt : ∀ {n} → X → RLE-Seq⁺ n → Set
    Alt x [ x₁ ]    = False (x X-≟ x₁)
    Alt x (x₁ ∷ xs) = False (x X-≟ x₁)
    Alt x (↑ l)     = Alt x l

  head : ∀ {n} → RLE-Seq⁺ n → X
  head [ x ]   = x
  head (x ∷ _) = x
  head (↑ l)   = head l

  head′ : ∀ {n} (p : Nonzero n) → Vec X n → X
  head′ {0} ()
  head′ _ (x ∷ _) = x

  data RLE-Seq : ℕ → Set ℓ where
    []  :                                 RLE-Seq 0
    ⟦_⟧ : ∀ {n p} → RLE-Seq⁺ (+_ n {p}) → RLE-Seq n

--

  decode⁺ : ∀ {n} → RLE-Seq⁺ n → Vec X (toℕ n)
  decode⁺ [ x ]   =      x ∷ []
  decode⁺ (x ∷ l) =      x ∷ decode⁺ l
  decode⁺ (↑ l)   = head l ∷ decode⁺ l

  decode : ∀ {n} → RLE-Seq n → Vec X n
  decode []    = []
  decode ⟦ x ⟧ = decode⁺ x

  encode⁺ : ∀ {n p} → Vec X n → RLE-Seq⁺ (+_ n {p})
  encode⁺ = proj₁ ∘ go
    where
      go : ∀ {n p} → (l : Vec X n)
         → Σ[ k ∈ RLE-Seq⁺ (+_ n {p}) ]
           (∀ {x} → ¬ (x ≡ head′ p l) → Alt x k)
      go {p = ()} []
      go (x ∷ []) = [ x ] , fromWitnessFalse
      go (x ∷ x₁ ∷ l) with x X-≟ x₁ | go (x₁ ∷ l)
      ... | yes x=x₁ | xs , alt = ↑ xs , alt ∘ (λ y≠x y=x₁ → contradiction (trans y=x₁ (sym x=x₁)) y≠x)
      ... | no  x≠x₁ | xs , alt = (x ∷ xs) {alt = alt x≠x₁} , fromWitnessFalse

  encode : ∀ {n} → Vec X n → RLE-Seq n
  encode []       = []
  encode (x ∷ xs) = ⟦ encode⁺ (x ∷ xs) ⟧
