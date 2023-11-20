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
