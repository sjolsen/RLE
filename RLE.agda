open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module RLE {a} (A : Set a) (_A-≟_ : Decidable {A = A} _≡_) where
  open import Data.Nat
  open import Nat-aux
  open import Data.Product
  open import Data.Unit using (⊤)
  open import Data.Vec
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Function
  open import Level using (Lift; lift)

  Nonzero : ℕ → Set
  Nonzero n = False (n ≟ 0)

  mutual
    infixr 5 [_,_]∷_
    data RLE-Seq : ℕ → Set a where
      []      : RLE-Seq 0
      [_,_]∷_ : ∀ (a : ℕ) (x : A) {b} (l : RLE-Seq b) → {p₁ : Nonzero a} {p₂ : Alt x l} → RLE-Seq (a + b)

    Alt : ∀ {n} → A → RLE-Seq n → Set
    Alt x []              = ⊤
    Alt x ([ _ , x₁ ]∷ l) = False (x A-≟ x₁)

--

  decode : ∀ {n} → RLE-Seq n → Vec A n
  decode []             = []
  decode ([ n , x ]∷ l) = replicate {n = n} x ++ (decode l)

  private
    rleHead : ∀ {n} → Nonzero n → RLE-Seq n → A
    rleHead () []
    rleHead _ ([ n , x ]∷ l) = x

    head′ : ∀ {n} → Nonzero n → Vec A n → A
    head′ () []
    head′ _  (x ∷ _) = x

    Alt′ : ∀ {n} → A → Vec A n → Set
    Alt′ x []       = ⊤
    Alt′ x (x₁ ∷ l) = False (x A-≟ x₁)

    xrefl : ∀ {ℓ} {X : Set ℓ} → (x : X) → (x ≡ x)
    xrefl x = refl

    popRun : ∀ {n} {p : Nonzero n}
           → (l : Vec A n)
           → Σ[ a ∈ ℕ ]
             Σ[ x ∈ A ]
             Σ[ b ∈ ℕ ]
             Σ[ j ∈ Vec A b ]
               Nonzero a
             × Alt′ x j
             × x ≡ head′ p l
             × a + b ≡ n
    popRun {zero} {}
    popRun {suc zero}    (x ∷ []) = 1 , x , _ , [] , _ , _ , refl , refl
    popRun {suc (suc _)} (x ∷ x₁ ∷ l) with (x A-≟ x₁)
    ... | yes q = let (a , y , b , j , p₁ , p₂ , p₃ , p₄) = popRun (x₁ ∷ l) in
                  1 + a , x , _ , j      , _ , subst₂ Alt′ (trans p₃ (sym q)) (xrefl j) p₂ , refl , cong suc p₄
    ... | no ¬q = 1     , x , _ , x₁ ∷ l , _ , fromWitnessFalse ¬q                         , refl , refl

  encode : ∀ {n} → Vec A n → RLE-Seq n
  encode = proj₁ ∘ <-rec _ go _
    where
      open import Induction.WellFounded
      open import Induction.Nat
      open ≡-Reasoning

      smaller : ∀ a b n → Nonzero a → a + b ≡ n → b <′ n
      smaller zero     _ _ ()
      smaller (suc a′) b n p q = <′-lemma a′ b n q

      alt-helper : ∀ n → (p : Nonzero n)
                 → (j : Vec A n)
                 → (k : RLE-Seq n)
                 → (x : A)
                 → head′ p j ≡ rleHead p k
                 → ¬ (x ≡ head′ p j)
                 → ¬ (x ≡ rleHead p k)
      alt-helper 0 ()
      alt-helper _ p j k x eq x≠xⱼ with head′ p j | rleHead p k
      ... | xⱼ | xₖ = λ x=xₖ → x≠xⱼ (trans x=xₖ (sym eq))

      Alt-helper : ∀ {n} x
                 → (p : Nonzero n)
                 → (l : RLE-Seq n)
                 → ¬ (x ≡ rleHead p l)
                 → Alt x l
      Alt-helper _ () [] _
      Alt-helper x _ ([ n , x₁ ]∷ l) alt = fromWitnessFalse alt

      Go : ∀ n (l : Vec A n) (k : RLE-Seq n) → Set a
      Go 0       l k = Lift ⊤
      Go (suc _) l k = rleHead _ k ≡ head′ _ l

      Go′ : ∀ m n → m ≡ n → (l : Vec A n) (k : RLE-Seq m) → Set a
      Go′ 0       0       _ l k = Lift ⊤
      Go′ 0       (suc _) ()
      Go′ (suc _)       0 ()
      Go′ (suc _) (suc _) _ l k = rleHead _ k ≡ head′ _ l

      go-helper : ∀ {a b n} {l : Vec A n}
                → (eq : a + b ≡ n)
                → Σ (RLE-Seq (a + b)) (Go′ (a + b) n eq l)
                → Σ (RLE-Seq n)       (Go n l)
      go-helper {n = 0}     eq (seq , go′) rewrite eq = seq , go′
      go-helper {n = suc _} eq (seq , go′) rewrite eq = seq , go′

      go : ∀ n → _ → (l : Vec A n) → Σ (RLE-Seq n) (Go n l)
      go 0 _ [] = [] , _
      go (suc n′) encode′ l with popRun l
      ... | 0      , x , b      , j       , () , p₂ , p₃ , p₄
      ... | suc a′ , x , 0      , []      , p₁ , p₂ , p₃ , p₄ =
        let seq = ([ suc a′ , x ]∷ [])
                    {p₁ = p₁}
        in go-helper {a = suc a′} {b = 0} {l = l} p₄ (seq , p₃)
      ... | suc a′ , x , suc b′ , xⱼ ∷ j′ , p₁ , p₂ , p₃ , p₄ with encode′ _ (smaller (suc a′) _ _ p₁ p₄) (xⱼ ∷ j′)
      ...   | rest , alt′ =
        let alt = alt-helper _ _ (xⱼ ∷ j′) rest x (sym alt′) (toWitnessFalse p₂)
            seq = ([ suc a′ , x ]∷ rest)
                    {p₁ = p₁}
                    {p₂ = Alt-helper x _ rest alt}
        in go-helper {a = suc a′} {b = suc b′} {l = l} p₄ (seq , p₃)
