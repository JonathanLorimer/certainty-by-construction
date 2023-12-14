module Chapter3-Proofs where

open import Chapter1-Agda
  using (Bool; true; false; _∧_; _∨_; not)

open import Chapter2-Numbers
  using (ℕ; zero; suc)


module Example-ProofsAsPrograms where
  open Chapter2-Numbers
    using (IsEven)
  
  open ℕ
  open IsEven

module Definition where
  data _≡_ {A : Set} : A → A → Set where
    refl : { x : A } → x ≡ x

  infix 4 _≡_

module Playground where  
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl)

  open Chapter2-Numbers

  _ : suc (suc (suc zero)) ≡ suc (suc (suc zero))
  _ = refl

  _ : 3 ≡ suc (suc (suc zero))
  _ = refl

  _ : 3 ≡ 1 + 2
  _ = refl

  0+x≡x : (x : ℕ) → 0 + x ≡ x
  0+x≡x _ = refl

  cong
    : { A B : Set }
    → {x y : A}
    → (f : A → B)
    → x ≡ y
    → f x ≡ f y
  cong f refl = refl

  x+0≡x : (x : ℕ) → x + 0 ≡ x
  x+0≡x zero = refl
  x+0≡x (suc x) = cong suc (x+0≡x x)

  +-identityˡ : (x : ℕ) → zero + x ≡ x 
  +-identityˡ = 0+x≡x 

  +-identityʳ : (x : ℕ) → x + zero ≡ x 
  +-identityʳ = x+0≡x

  *-identityˡ : (x : ℕ) → 1 * x ≡ x
  *-identityˡ zero = refl
  *-identityˡ (suc n) = cong suc (+-identityʳ n)

  *-identityʳ : (x : ℕ) → x * 1 ≡ x
  *-identityʳ zero = refl
  *-identityʳ (suc x) = cong suc (*-identityʳ x)

  ∸-identityʳ : (x : ℕ) → x ∸ 0 ≡ x 
  ∸-identityʳ _ = refl

  ^-identityʳ : (x : ℕ) → x ^ 1 ≡ x 
  ^-identityʳ zero = refl 
  ^-identityʳ (suc x) = cong suc (*-identityʳ x)

  ∨-identityˡ : (x : Bool) → false ∨ x ≡ x 
  ∨-identityˡ _ = refl

  ∨-identityʳ : (x : Bool) → x ∨ false ≡ x 
  ∨-identityʳ false = refl 
  ∨-identityʳ true = refl

  ∧-identityˡ : (x : Bool) → true ∧ x ≡ x 
  ∧-identityˡ _ = refl

  ∧-identityʳ : (x : Bool) → x ∧ true ≡ x 
  ∧-identityʳ false = refl 
  ∧-identityʳ true = refl

  *-zeroˡ : (x : ℕ) → zero * x ≡ zero 
  *-zeroˡ _ = refl

  *-zeroʳ : (x : ℕ) → x * zero ≡ zero 
  *-zeroʳ zero = refl 
  *-zeroʳ (suc x) = *-zeroʳ x

  ∨-zeroˡ : (x : Bool) → true ∨ x ≡ true 
  ∨-zeroˡ _ = refl

  ∨-zeroʳ : (x : Bool) → x ∨ true ≡ true 
  ∨-zeroʳ false = refl 
  ∨-zeroʳ true = refl

  ∧-zeroˡ : (x : Bool) → false ∧ x ≡ false 
  ∧-zeroˡ _ = refl

  ∧-zeroʳ : (x : Bool) → x ∧ false ≡ false 
  ∧-zeroʳ false = refl 
  ∧-zeroʳ true = refl

  sym : {A : Set} → { x y : A } → x ≡ y → y ≡ x
  sym refl = refl

  *-identityˡ′ : (x : ℕ) → x ≡ 1 * x 
  *-identityˡ′ x = sym (*-identityˡ x)

  sym-involutive : {A : Set} → {x y : A} → (p : x ≡ y) → sym (sym p) ≡ p
  sym-involutive refl = refl

  not-involutive : (x : Bool) → not (not x) ≡ x
  not-involutive false = refl
  not-involutive true = refl

  trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

  a^1≡a+b*0 : (a b : ℕ) → a ^ 1 ≡ a + b * 0 
  a^1≡a+b*0 a b 
    = trans (^-identityʳ a) 
    ( trans (sym (+-identityʳ a)) 
            (cong (a +_) (sym (*-zeroʳ b)))
    )

  _‽_⦂_ : { A : Set } → Bool → A → A → A
  false ‽ t ⦂ f = t
  true ‽ t ⦂ f = f

  infixr 20 _‽_⦂_

  case_of_ : {A B : Set} → A → (A → B) → B 
  case e of f = f e

  module ≡-Reasoning where
    _∎ : {A : Set} → (x : A) → x ≡ x
    _∎ x = refl

    infix 3 _∎
    
    _≡⟨⟩_ : {A : Set} {y : A}
          → (x : A)
          → x ≡ y
          → x ≡ y
    x ≡⟨⟩ p = p

    infixr 2 _≡⟨⟩_

    _ : 4 ≡ suc (1 + 2)
    _ =
      4 ≡⟨⟩
      2 + 2 ≡⟨⟩
      suc 1 + 2 ≡⟨⟩
      suc (1 + 2) ∎
    
    _≡⟨_⟩_ 
      : { A : Set }
      → (x : A)
      → {y z : A}
      → x ≡ y
      → y ≡ z
      → x ≡ z
    x ≡⟨ j ⟩ p = trans j p
    
    infixr 2 _≡⟨_⟩_

    begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
    begin_ x=y = x=y

    infix 1 begin_

  open ≡-Reasoning

  a^1≡a+b*0′ : (a b : ℕ) → a ^ 1 ≡ a + b * 0 
  a^1≡a+b*0′ a b = 
    begin 
      a ^ 1 
    ≡⟨ ^-identityʳ a ⟩ 
      a 
    ≡⟨ sym (+-identityʳ a) ⟩
      a + 0 
    ≡⟨ cong (a +_) (sym (*-zeroʳ b)) ⟩ 
      a + b * 0 
    ∎

  
  ∨-assoc : (a b c : Bool) → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c) 
  ∨-assoc false b c = refl
  ∨-assoc true b c = refl

  +-assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc zero y z = refl
  +-assoc (suc x) y z = 
      begin
      suc x + y + z
      ≡⟨ cong suc (+-assoc x y z) ⟩
      suc x + (y + z)
      ∎

  +-suc : (x y : ℕ) → x + suc y ≡ suc (x + y) 
  +-suc zero y = refl 
  +-suc (suc x) y = cong suc (+-suc x y)

  
  +-comm : (x y : ℕ) → x + y ≡ y + x
  +-comm zero y = sym (+-identityʳ y)
  +-comm (suc x) y = begin
    suc x + y
    ≡⟨ cong suc (+-comm x y) ⟩
    suc (y + x)
    ≡⟨ sym (+-suc y x) ⟩
    y + suc x
    ∎

  suc-injective : {x y : ℕ} → suc x ≡ suc y → x ≡ y 
  suc-injective refl = refl
  
  *-suc : (x y : ℕ) → x * suc y ≡ x + x * y
  *-suc zero y = refl
  *-suc (suc x) y = begin
    suc (y + x * suc y)
    ≡⟨ cong suc (+-comm y (x * suc y)) ⟩
    suc (x * suc y + y)
    ≡⟨ cong suc (cong (_+ y) (*-suc x y)) ⟩
    suc ((x + x * y) + y)
    ≡⟨ cong suc (+-assoc x (x * y) y)⟩
    suc (x + (x * y + y))
    ≡⟨ cong suc (cong (x +_) (+-comm (x * y) y)) ⟩
    suc x + (y + x * y)
    ≡⟨⟩
    suc x + (suc x * y)
    ∎

  *-comm : (x y : ℕ) → x * y ≡ y * x 
  *-comm zero y = sym (*-zeroʳ y) 
  *-comm (suc x) y = begin 
    suc x * y 
    ≡⟨⟩ 
    y + x * y 
    ≡⟨ cong (y +_) (*-comm x y) ⟩ 
    y + y * x 
    ≡⟨ sym (*-suc y x) ⟩ 
    y * suc x 
    ∎

  *-distribʳ-+ : (x y z : ℕ) → (y + z) * x ≡ y * x + z * x 
  *-distribʳ-+ x zero z = refl 
  *-distribʳ-+ x (suc y) z = begin 
    (suc y + z) * x 
    ≡⟨⟩ 
    x + (y + z) * x 
    ≡⟨ cong (x +_) (*-distribʳ-+ x y z) ⟩ 
    x + (y * x + z * x) 
    ≡⟨ sym (+-assoc x (y * x) (z * x)) ⟩ 
    (x + y * x) + z * x 
    ≡⟨⟩ 
    suc y * x + z * x 
    ∎

  *-distribˡ-+ : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z 
  *-distribˡ-+ x y z = begin 
    x * (y + z) 
    ≡⟨ *-comm x _ ⟩ 
    (y + z) * x 
    ≡⟨ *-distribʳ-+ x y z ⟩ 
    y * x + z * x 
    ≡⟨ cong (_+ z * x) (*-comm y x) ⟩ 
    x * y + z * x 
    ≡⟨ cong (x * y +_) (*-comm z x) ⟩ 
    x * y + x * z
    ∎

  *-assoc : (x y z : ℕ) → (x * y) * z ≡ x * (y * z) 
  *-assoc zero y z = refl 
  *-assoc (suc x) y z = begin 
    suc x * y * z 
    ≡⟨⟩ 
    (y + x * y) * z 
    ≡⟨ *-distribʳ-+ z y (x * y) ⟩ 
    y * z + (x * y) * z
    ≡⟨ cong (y * z +_) (*-assoc x y z) ⟩ 
    y * z + x * (y * z) 
    ≡⟨⟩ 
    suc x * (y * z) 
    ∎

open import Relation.Binary.PropositionalEquality 
  using (_≡_; module ≡-Reasoning) 
  public

module PropEq where 
  open Relation.Binary.PropositionalEquality 
    using (refl; cong; sym; trans) 
    public

open import Data.Bool using (if_then_else_) public 
open import Function using (case_of_) public

open import Data.Bool.Properties 
  using ( ∨-identityˡ ; ∨-identityʳ 
        ; ∨-zeroˡ     ; ∨-zeroʳ 
        ; ∨-assoc     ; ∧-assoc 
        ; ∧-identityˡ ; ∧-identityʳ 
        ; ∧-zeroˡ     ; ∧-zeroʳ 
        ; not-involutive 
        ) 
  public

open import Data.Nat.Properties 
  using ( +-identityˡ ; +-identityʳ 
        ; *-identityˡ ; *-identityʳ
        ; *-zeroˡ     ; *-zeroʳ 
        ; +-assoc     ; *-assoc 
        ; +-comm      ; *-comm
        ; ^-identityʳ 
        ; +-suc       ; suc-injective 
        ; *-distribˡ-+ ; *-distribʳ-+
        )
  public
