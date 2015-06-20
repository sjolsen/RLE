module RLE where
  import Data.Fin as Fin
  open import Data.Digit
  open import Data.Nat renaming (_≟_ to _ℕ-≟_)
  open import Data.Product
  open import Data.Vec as Vec
  open import Digit-aux renaming (_≟_ to _Digit-≟_)
  open import Function
  open import Nat-aux
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation

-- Data definitions

  record Run : Set where
    constructor run
    field
      value     : Bit
      length    : ℕ
      {nonzero} : False (length ℕ-≟ 0)
  open Run

  RLE-Seq : ℕ → Set
  RLE-Seq = Vec Run

-- Encoding and decoding

  popRun : ∀ m → Vec Bit (suc m)
         → Σ[ a ∈ ℕ ]
           Σ[ b ∈ ℕ ]
           Σ[ r ∈ Run ]
           Σ[ j ∈ Vec Bit b ]
           a + b ≡ suc m × length r ≡ a
  popRun zero    (x ∷ []) = 1 , 0 , run x 1 , [] , refl , refl
  popRun (suc m) (x ∷ l)  = let (a , b , r , j , p₁ , p₂) = popRun m l in
    case (x Digit-≟ value r) of λ {
      (yes _) → suc a , b       , run x (suc a) , j , cong (_+_ 1) p₁   , refl ;
      (no  _) → suc 0 , (suc m) , run x (suc 0) , l , cong (_+_ 2) refl , refl
    }

  encode : ∀ m → Vec Bit m → Σ[ n ∈ ℕ ] RLE-Seq n
  encode = <-rec _ go
    where
      open import Induction.WellFounded
      open import Induction.Nat

      smaller : ∀ a b m r → a + b ≡ suc m → length r ≡ a → b <′ suc m
      smaller zero     _ _ r _ p = contradiction p (toWitnessFalse (nonzero r))
      smaller (suc a′) b m _ x _ = s≤′s b m (+→≤′-lemmaʳ a′ b m (suc-inj x))

      go : ∀ m → _ → Vec Bit m → Σ[ n ∈ ℕ ] RLE-Seq n
      go zero    encode′ [] = 0 , []
      go (suc m) encode′ l  =
        let (a , b , r , j , p₁ , p₂) = popRun m l
            (n , rest)                = encode′ b (smaller a b m r p₁ p₂) j
        in suc n , r ∷ rest

  decode : ∀ n → RLE-Seq n → Σ[ m ∈ ℕ ] Vec Bit m
  decode 0       []      = 0 , []
  decode (suc n) (x ∷ l) = let (m , rest) = decode n l in
    length x + m , (replicate {n = length x} (value x)) ++ rest
