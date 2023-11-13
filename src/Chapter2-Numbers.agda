module Chapter2-Numbers where

import Chapter1-Agda

module Definition-Naturals where
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

module Sandbox-Naturals where
  open import Data.Nat
    using (ℕ; zero; suc)

  open Chapter1-Agda 
    using (Bool; true; false)

  n=0? : ℕ → Bool
  n=0? zero = true
  n=0? (suc x) = false

  even? : ℕ → Bool
  even? zero = true
  even? (suc zero) = false
  even? (suc (suc x)) = even? x

  data Evenℕ : Set where
    zero : Evenℕ
    suc-suc : Evenℕ → Evenℕ

  toℕ : Evenℕ → ℕ
  toℕ zero = zero
  toℕ (suc-suc n) = suc (suc (toℕ n))

  module Sandbox-Usable where
    postulate
      Usable : Set
      Unusable : Set

    IsEven : ℕ → Set
    IsEven zero = Usable
    IsEven (suc zero) = Unusable
    IsEven (suc (suc x)) = IsEven x

  data IsEven : ℕ → Set where
    zero-even : IsEven zero
    suc-suc-even : {n : ℕ} → IsEven n → IsEven (suc (suc n))

  data IsOdd : ℕ → Set where
    is-odd : {n : ℕ} → IsEven n → IsOdd (suc n)

  evenOdd : {n : ℕ} → IsEven n → IsOdd (suc n)
  evenOdd = is-odd

  data Maybe (A : Set) : Set where
    just : A → Maybe A
    nothing : Maybe A
  
  evenEv : (n : ℕ) → Maybe (IsEven n)
  evenEv zero = just zero-even
  evenEv (suc zero) = nothing
  evenEv (suc (suc n)) with evenEv n
  ... | just x = just (suc-suc-even x)
  ... | nothing = nothing

  infixl 6 _+_
  _+_ : ℕ → ℕ → ℕ
  zero + y = y
  suc x + y = suc (x + y)

  infixl 7 _*_
  _*_ : ℕ → ℕ → ℕ
  zero * b = zero
  suc a * b = b + a * b

  _^_ : ℕ → ℕ → ℕ
  a ^ zero = suc zero
  a ^ suc b = a * a ^ b

  _∸_ : ℕ → ℕ → ℕ
  x ∸ zero = x
  zero ∸ suc y = zero
  suc x ∸ suc y = x ∸ y

  module Natural-Test where
    open import Relation.Binary.PropositionalEquality

    _ : 1 + 2 ≡ 3
    _ = refl

    _ : 3 ∸ 1 ≡ 2
    _ = refl

module Misstep-Integers₁ where
  data ℤ : Set where
    zero : ℤ 
    suc : ℤ → ℤ
    pred : ℤ → ℤ

module Misstep-Integers₂ where
  import Data.Nat as ℕ
  open ℕ using (ℕ; zero; suc)
  
  record ℤ : Set where
    constructor mkℤ
    field 
      pos : ℕ
      neg : ℕ

module Misstep-Integers₃ where
  open import Data.Nat
  
  data ℤ : Set where
    +_ : ℕ → ℤ
    -_ : ℕ → ℤ

  -- Issue
  _ : ℤ
  _ = + 0

  _ : ℤ
  _ = - 0

module Sandbox-Integers where
  import Data.Nat as ℕ
  open ℕ using (ℕ)

  data ℤ : Set where
    +_ : ℕ → ℤ
    -[1+_] : ℕ → ℤ
  
  0ℤ : ℤ
  0ℤ = + 0

  -1ℤ : ℤ
  -1ℤ = -[1+ 0 ]

  suc : ℤ → ℤ
  suc (+ x) = + ℕ.suc x
  suc -[1+ ℕ.zero ] = 0ℤ
  suc -[1+ ℕ.suc x ] = -[1+ x ]

  pred : ℤ → ℤ
  pred (+ ℕ.zero) = -1ℤ
  pred (+ ℕ.suc x) = + x
  pred -[1+ x ] = -[1+ ℕ.suc x ]

  pattern +[1+_] n = + ℕ.suc n
  pattern +0 = + ℕ.zero

  -_ : ℤ → ℤ 
  - +0 =  +0
  - +[1+ x ] = -[1+ x ] 
  - -[1+ x ] = +[1+ x ] 

  _⊖_ : ℕ → ℕ → ℤ 
  ℕ.zero ⊖ ℕ.zero = +0
  ℕ.zero ⊖ ℕ.suc n = -[1+ n ]
  ℕ.suc n ⊖ ℕ.zero = +[1+ n ]
  ℕ.suc x ⊖ ℕ.suc y = x ⊖ y

  infixl 5 _+_
  
  _+_ : ℤ → ℤ → ℤ
  + x + + y = + (x ℕ.+ y)
  + x + -[1+ y ] = x ⊖ ℕ.suc y
  -[1+ x ] + + y = y ⊖ ℕ.suc x 
  -[1+ x ] + -[1+ y ] = -[1+ x ℕ.+ ℕ.suc y ]

  infixl 5 _-_
  _-_ : ℤ → ℤ → ℤ
  x - y = x + (- y)

  infixl 6 _*_
  _*_ : ℤ → ℤ → ℤ
  x * +0 = +0
  x * +[1+ ℕ.zero ] = x
  x * -[1+ ℕ.zero ] = - x
  x * +[1+ ℕ.suc n ] = (x * +[1+ n ]) + x
  x * -[1+ ℕ.suc n ] = (x * -[1+ n ]) - x


  module Mult-Tests where
    open import Relation.Binary.PropositionalEquality

    _ : + 2 * + 2 ≡ + 4
    _ = refl

    _ : -[1+ 1 ] * + 2 ≡ -[1+ 3 ]
    _ = refl

    _ : + 2 * -[1+ 1 ] ≡ -[1+ 3 ]
    _ = refl
  
open import Data.Nat 
  using (ℕ; zero; suc; _+_; _*_; _^_; _∸_) 
  public

open Sandbox-Naturals 
  using (IsEven) 
  renaming ( zero-even to z-even ; suc-suc-even to ss-even ) 
  public

open import Data.Maybe 
  using (Maybe; just; nothing) 
  public
