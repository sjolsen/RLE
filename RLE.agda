module RLE where
  import Data.Fin as Fin
  open import Data.Digit
  open import Data.Nat renaming (_≟_ to _ℕ-≟_)
  open import Data.Product
  open import Data.Unit
  open import Data.Vec
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

  infixr 5 _∷_
  mutual
    data RLE-Seq : ℕ → Set where
      []  : RLE-Seq 0
      _∷_ : ∀ {s} r (l : RLE-Seq s) {p : Alt r l} → RLE-Seq (length r + s)

    Alt : ∀ {n} → Run → RLE-Seq n → Set
    Alt _ []       = ⊤
    Alt r (r₁ ∷ l) = False (value r Digit-≟ value r₁)

-- Encoding and decoding

  Alt′ : ∀ {n} → Bit → Vec Bit n → Set
  Alt′ _ []       = ⊤
  Alt′ x (x₁ ∷ l) = False (x Digit-≟ x₁)

  head′ : ∀ {a n} {A : Set a} → False (n ℕ-≟ 0) → Vec A n → A
  head′ {n = zero}  () _
  head′ {n = suc n} _  (x ∷ _) = x

  xrefl : ∀ {a} {A : Set a} (x : A) → x ≡ x
  xrefl x = refl

  record PopRunT (n : ℕ) (x : Bit) : Set where
    constructor pop[_,_,_,_,_,_,_,_]
    field
      a   : ℕ
      b   : ℕ
      r   : Run
      j   : Vec Bit b
      p₁  : a + b ≡ n
      p₂  : length r ≡ a
      p₃  : value r ≡ x
      p₄  : Alt′ (value r) j

  popRun : ∀ n {nz : False (n ℕ-≟ 0)} → (l : Vec Bit n) → PopRunT n (head′ nz l)
  popRun 0 {} _
  popRun 1 (x ∷ []) = pop[ 1 , 0 , run x 1 , [] , refl , refl , refl , _ ]
  popRun (suc (suc _)) (x ∷ x₁ ∷ l) with (x Digit-≟ x₁)
  ... | yes q = let pop[ a , b , r , j , p₁ , p₂ , p₃ , p₄ ] = popRun _ (x₁ ∷ l) in
                pop[ 1 + a , b , run x (1 + a) , j      , cong suc p₁ , refl , refl , subst₂ Alt′ (trans p₃ (sym q)) (xrefl j) p₄ ]
  ... | no ¬q = pop[ 1     , _ , run x 1       , x₁ ∷ l , refl        , refl , refl , fromWitnessFalse ¬q ]

  encode : ∀ n → Vec Bit n → RLE-Seq n
  encode n l = proj₁ $ <-rec _ go n l
    where
      open import Induction.WellFounded
      open import Induction.Nat
      open ≡-Reasoning

      smaller : ∀ a b n r → a + b ≡ n → length r ≡ a → b <′ n
      smaller zero     _ _ r _ p = contradiction p (toWitnessFalse (nonzero r))
      smaller (suc a′) b n _ x _ = <′-lemma a′ b n x

      go : ∀ n → _ → Vec Bit n → RLE-Seq n × ⊤
      go zero     encode′ [] = [] , _
      go (suc n′) encode′ l  =
        let pop[ a , b , r , j , p₁ , p₂ , p₃ , p₄ ] = popRun _ l
            (rest , _)                               = encode′ b (smaller a b (suc n′) r p₁ p₂) j
            index                                    = begin
                                                         length r + b ≡⟨ cong₂ _+_ p₂ refl ⟩
                                                         a        + b ≡⟨ p₁ ⟩
                                                         suc n′       ∎
        in (subst id (cong RLE-Seq index) (_∷_ r rest {p = {!!}})) , _


  decode : ∀ {n} → RLE-Seq n → Vec Bit n
  decode []      = []
  decode (r ∷ l) = replicate {n = length r} (value r) ++ decode l
