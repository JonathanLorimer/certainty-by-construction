module Chapter1-Agda where

module Example-Imports where
  open import Data.Bool
  
  _ : Bool
  _ = false

module Example-TypingJudgments where
  postulate
    Bool : Set
    false : Bool
    true : Bool

module Booleans where
  data Bool : Set where
    false : Bool
    true : Bool

  not : Bool → Bool
  not false = true
  not true = false

  open import Relation.Binary.PropositionalEquality

  _ : not (not false) ≡ false
  _ = refl
  
  _∧_ : Bool -> Bool -> Bool
  false ∧ other = false
  true ∧ other = other

  _∨_ : Bool -> Bool -> Bool
  true ∨ other = true
  false ∨ other = other

  postulate always-stuck : Bool

module Example-Employees where
  open Booleans
  open import Data.String
    using (String)

  data Department : Set where
    administrative : Department
    engineering : Department 
    finance : Department 
    marketing : Department 
    sales : Department
  
  record Employee : Set where
    field
      name : String
      department : Department
      is-new-hire : Bool
   
module Sandbox-Tuples where
  record _×_ (A : Set) (B : Set) : Set where
    field
      proj₁ : A
      proj₂ : B

  open Booleans

  my-tuple : Bool × Bool 
  my-tuple = record { proj₁ = true ∨ true ; proj₂ = not true }

  open _×_

  my-copattern : Bool × Bool
  proj₁ my-copattern = true
  proj₂ my-copattern = false

  _,_ : {A B : Set} → A → B → A × B 
  x , x₁ = record { proj₁ = x ; proj₂ = x₁ }

module Sandbox-Tuples₂ where 
  open Booleans 
  
  record _×_ (A : Set) (B : Set) : Set where 
    constructor _,_ 
    field 
      proj₁ : A 
      proj₂ : B 

  open _×_



module Sandbox-Implicits where
  open import Data.Bool
    using (Bool; false; true; not; _∨_)

  open import Data.Product
    using (_×_; proj₁; proj₂)
    renaming ( _,′_ to _,_ 
             ; curry′ to curry 
             ; uncurry′ to uncurry 
             )

  mk-tuple : (A : Set) → (B : Set) → A → B → A × B 
  mk-tuple A B x x₁ = x , x₁

  
