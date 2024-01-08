module Chapter6-Decidability where

open import Chapter1-Agda using (Bool; true; false)
open import Chapter2-Numbers using (ℕ; zero; suc; _+_)
open import Chapter3-Proofs using (_≡_; module PropEq; module ≡-Reasoning; suc-injective)
open PropEq
open import Chapter4-Relations using (Level; _⊔_; lsuc; Σ; _,_)

module Sandbox-Explosion where
  _IsFalse : Set → Set₁
  P IsFalse = P → { A : Set } → A

  2≢3 : (2 ≡ 3) IsFalse
  2≢3 ()

module Definition-Bottom where
  data ⊥ : Set where

  2≢3 : 2 ≡ 3 → ⊥ 
  2≢3 ()

  ⊥-elim : {A : Set} → ⊥ → A
  ⊥-elim ()

  ¬_ : { ℓ : Level } → Set ℓ → Set ℓ
  ¬ P = P → ⊥
  infix 3 ¬_

  _≢_ : { A : Set } → A → A → Set
  x ≢ y = ¬ x ≡ y
  infix 4 _≢_

  ≢-sym : {A : Set} {x y : A} → x ≢ y → y ≢ x 
  ≢-sym x≢y y=x = x≢y (sym y=x)

  Reflexive 
    : { c ℓ : Level } { A : Set c }
    → (A → A → Set ℓ)
    → Set (ℓ ⊔ c)
  Reflexive {A = A} _≈_ = {x : A} → x ≈ x

  ≡-refl : { A : Set } → Reflexive {A = A} _≡_
  ≡-refl = refl

  ¬≢-refl : ¬ ({A : Set} → Reflexive {A = A} _≢_)
  ¬≢-refl ¬≡-refl = ¬≡-refl {ℕ} {0} refl

  Transitive  
    : { c ℓ : Level} {A : Set c}
    → (A → A → Set ℓ)
    → Set (c ⊔ ℓ)
  Transitive {A = A} _≈_ = {x y z : A} → x ≈ y → y ≈ z → x ≈ z
  
  ¬≢-trans : ¬ ({ A : Set } → Transitive {A = A} _≢_)
  ¬≢-trans ≢-trans = ≢-trans {ℕ} 2≢3 (≢-sym 2≢3) refl

open import Relation.Nullary
  using (¬_)

module Example-NoMonusLeftIdentity where
  open Chapter2-Numbers using (_∸_)
  
  ¬∸identityˡ : ¬ Σ ℕ (λ e → (x : ℕ) → e ∸ x ≡ x)
  ¬∸identityˡ (e , e-is-id)
    with e-is-id 0 | e-is-id 1
  ... | refl | ()

  
module Sandbox-Decidability where
  open Chapter2-Numbers
    using (Maybe; just; nothing)
  
  data Dec {ℓ : Level} (P : Set ℓ) : Set ℓ where
    yes : P → Dec P
    no : ¬ P → Dec P

open import Relation.Nullary 
  using (Dec; yes; no) 

module Nat-Properties where 
  _==_ : ℕ → ℕ → Bool 
  zero == zero = true 
  zero == suc y = false 
  suc x == zero = false 
  suc x == suc y = x == y

  _≟_ : (x y : ℕ) → Dec (x ≡ y)
  zero ≟ zero = yes refl
  zero ≟ suc y = no λ { () }
  suc x ≟ zero = no λ { () }
  suc x ≟ suc y with x ≟ y
  ... | yes refl = yes refl
  ... | no x≢y = no λ { refl → x≢y refl }

  DecidableEquality : {ℓ : Level} (A : Set ℓ) → Set ℓ 
  DecidableEquality A = (x y : A) → Dec (x ≡ y)

  _≟ℕ_ : DecidableEquality ℕ 
  _≟ℕ_ = _≟_

  map-dec : {ℓ₁ ℓ₂ : Level} {P : Set ℓ₁} {Q : Set ℓ₂} 
    → (P → Q) → (Q → P) 
    → Dec P → Dec Q 
  map-dec to from (yes p) = yes (to p) 
  map-dec to from (no ¬p) = no (λ q → ¬p (from q))

open import Relation.Binary using (DecidableEquality)

module BinaryTrees where

  data BinTree {ℓ : Level} (A : Set ℓ) : Set ℓ where
    empty : BinTree A
    branch : BinTree A → A → BinTree A → BinTree A


  pattern leaf a = branch empty a empty

  is-singleton : {A : Set} → BinTree A → Bool
  is-singleton (leaf _) = true
  is-singleton _ = false

  tree : BinTree ℕ
  tree = 
    branch
      (branch (leaf 0) 0 (leaf 4))
      2
      (leaf 6)

  private variable 
    ℓ : Level 
    A : Set ℓ 
    a b : A 
    l r : BinTree A

  data _∈_ : A → BinTree A → Set where
    here :  a ∈ branch l a r
    left :  a ∈ l → a ∈ branch l b r
    right : a ∈ r → a ∈ branch l b r

  6∈tree : 6 ∈ tree
  6∈tree = right here

  Decidable : {c ℓ : Level} {A : Set c} 
            → (A → Set ℓ) → Set (c ⊔ ℓ) 
  Decidable {A = A} P = (a : A) → Dec (P a)

  Decidable₂ : {c ℓ : Level} {A : Set c} 
             → (A → A → Set ℓ) → Set (c ⊔ ℓ)
  Decidable₂ {A = A} _~_ = (x y : A) → Dec (x ~ y)

  ∈? : DecidableEquality A → (t : BinTree A) → Decidable (_∈ t) 
  ∈? _≟_ empty a = no λ { () }
  ∈? _≟_ (branch l x r) a with x ≟ a 
  ... | yes refl = yes here 
  ... | no x≢a with ∈? _≟_ l a 
  ...   | yes x∈l = yes (left x∈l)
  ...   | no x∉l with ∈? _≟_ r a
  ...     | yes x∈r = yes (right x∈r)
  ...     | no x∉r = no λ { here → x≢a refl
                          ; (left x∈l) → x∉l x∈l
                          ; (right x∈r) → x∉r x∈r 
                          }

  data All {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (P : A → Set ℓ₂) : BinTree A → Set (ℓ₁ ⊔ ℓ₂) where 
    empty : All P empty 
    branch : All P l → P a → All P r → All P (branch l a r)

  pattern leaf a = branch empty a empty

  open Chapter2-Numbers using (IsEven; z-even; ss-even)

  tree-all-even : All IsEven tree
  tree-all-even = 
    branch 
      (branch (branch empty z-even empty) z-even (branch empty (ss-even (ss-even z-even)) empty)) 
      (ss-even z-even) 
      (branch empty (ss-even (ss-even (ss-even z-even))) empty)

  
  all? : {P : A → Set} → Decidable P → Decidable (All P)
  all? p? empty = yes empty
  all? p? (branch l a r) with p? a
  ... | no ¬Pa = no λ { (branch _ Pa _) → ¬Pa Pa }
  ... | yes Pa 
     with all? p? l | all? p? r 
  ...   | no ¬allPl | _ = no λ { (branch allPl _ _) → ¬allPl allPl }
  ...   | yes _     | no ¬allPr = no λ { (branch _ _ allPr) → ¬allPr allPr }
  ...   | yes Pl    | yes Pr = yes (branch Pl Pa Pr)

  data IsBST {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (_<_ : A → A → Set ℓ₂) 
    : BinTree A → Set (ℓ₁ ⊔ ℓ₂) where
    bst-empty : IsBST _<_ empty 
    bst-branch 
      : All (_< a) l 
      → All (a <_) r 
      → IsBST _<_ l 
      → IsBST _<_ r 
      → IsBST _<_ (branch l a r)

  open Chapter4-Relations using (_≤_; z≤n; s≤s; _<_)

  is-bst? : {_≤_ : A → A → Set} → Decidable₂ _≤_ → Decidable (IsBST _≤_) 
  is-bst? _≤?_ empty = yes bst-empty 
  is-bst? _≤?_ (branch l a r) 
    with all? (_≤? a) l 
  ... | no l≰ = no λ { (bst-branch l≤ _ _ _) → l≰ l≤ } 
  ... | yes l≤ 
    with all? (a ≤?_) r 
  ... | no ≰r = no λ { (bst-branch _ ≤r _ _) → ≰r ≤r } 
  ... | yes ≤r 
    with is-bst? _≤?_ l 
  ... | no ¬bst-l = no λ { (bst-branch _ _ bst-l _) → ¬bst-l bst-l } 
  ... | yes bst-l 
    with is-bst? _≤?_ r 
  ... | no ¬bst-r = no λ { (bst-branch _ _ _ bst-r) → ¬bst-r bst-r } 
  ... | yes bst-r = yes (bst-branch l≤ ≤r bst-l bst-r)

  data Tri {a b c : Level} (A : Set a) (B : Set b) (C : Set c)
         : Set (a ⊔ b ⊔ c) where
    tri< :   A → ¬ B → ¬ C → Tri A B C 
    tri≈ : ¬ A →   B → ¬ C → Tri A B C
    tri> : ¬ A → ¬ B →   C → Tri A B C 
  
  Trichotomous
    : {ℓ eq lt : Level}
    → {A : Set ℓ}
    → (_≈_ : A → A → Set eq)
    → (_<_ : A → A → Set lt)
    → Set (lt ⊔ eq ⊔ ℓ)
  Trichotomous {A = A} _≈_ _<_ =
    (x y : A) → Tri (x < y) (x ≈ y) (y < x)

  refute : {x y : ℕ} → ¬ x < y → ¬ suc x < suc y
  refute x≮y (s≤s x<y) = x≮y x<y

  <-cmp : Trichotomous _≡_ _<_
  <-cmp zero zero = tri≈ (λ ()) refl (λ ())
  <-cmp zero (suc y) = tri< (s≤s z≤n) (λ ()) (λ ())
  <-cmp (suc x) zero = tri> (λ ()) (λ ()) (s≤s z≤n)
  <-cmp (suc x) (suc y) with <-cmp x y
  ... | tri< x<y x≉y x≱y 
      = tri< (s≤s x<y) 
             (λ { sx≈sy → x≉y (suc-injective sx≈sy) }) 
             (refute x≱y)
  ... | tri≈ x≮y x≈y x≱y
      = tri≈ (refute x≮y)
             (cong suc x≈y) 
             (refute x≱y)
  ... | tri> x≮y x≉y x≥y 
      = tri> (refute x≮y)
             (λ { sx≈sy → x≉y (suc-injective sx≈sy) })
             (s≤s x≥y)

  
  module _ 
    {ℓ : Level}
    {_<_ : A → A → Set ℓ}
    (<-cmp : Trichotomous _≡_ _<_) where
  
    insert 
      : A
      → BinTree A
      → BinTree A
    insert a empty = leaf a
    insert a (branch l x r) with <-cmp a x
    ... | tri< x₁ x₂ x₃ = branch (insert a l) x r
    ... | tri≈ x₁ x₂ x₃ = branch l x r
    ... | tri> x₁ x₂ x₃ = branch l x (insert a r)

    all-insert
      : {P : A → Set ℓ}  
      → (a : A) → P a → {t : BinTree A}  
      → All P t → All P (insert a t)
    all-insert a pa empty = leaf pa
    all-insert a pa {branch l x r} (branch l<x px x<r)
      with <-cmp a x
    ... | tri< a<x _ _ = branch (all-insert a pa l<x) px x<r
    ... | tri≈ _ a=x _ = branch l<x px x<r
    ... | tri> _ _ x<a = branch l<x px (all-insert a pa x<r)

    bst-insert 
      : (a : A) 
      → {t : BinTree A} 
      → IsBST _<_ t 
      → IsBST _<_ (insert a t) 
    bst-insert a bst-empty = bst-branch empty empty bst-empty bst-empty
    bst-insert a {branch l x r} (bst-branch l<x x<r lbst rbst)
      with <-cmp a x
    ... | tri< a<x _ _ = 
            bst-branch 
              (all-insert a a<x l<x) 
              x<r 
              (bst-insert a lbst)
              rbst
    ... | tri≈ _ a=x _ = bst-branch l<x x<r lbst rbst
    ... | tri> _ _ x<a =
            bst-branch 
              l<x
              (all-insert a x<a x<r)
              lbst
              (bst-insert a rbst)

module Intrinsic-BST-Impl
  { c ℓ : Level } {A : Set c} (_<_ : A → A → Set ℓ) where

  data BST (lo hi : A) : Set (c ⊔ ℓ) where
    empty : lo < hi → BST lo hi
    xbranch
      : (a : A)
      → BST lo a
      → BST a hi
      → BST lo hi

  pattern branch lo a hi = xbranch a lo hi
  pattern leaf lo<a a a<hi = branch (empty lo<a) a (empty a<hi)

  open BinaryTrees using (Trichotomous; Tri)
  open Tri

  insert 
    : {lo hi : A} 
    → (<-cmp : Trichotomous _≡_ _<_) 
    → (a : A) 
    → lo < a 
    → a < hi 
    → BST lo hi 
    → BST lo hi 
  insert <-cmp a lo<a a<hi (empty _) = leaf lo<a a a<hi 
  insert <-cmp a lo<a a<hi (branch l x r) 
    with <-cmp a x 
  ... | tri< a<x _ _ = branch (insert <-cmp a lo<a a<x l) x r 
  ... | tri≈ _ a=x _ = branch l x r 
  ... | tri> _ _ x<a = branch l x (insert <-cmp a x<a a<hi r) 

open BinaryTrees using (Trichotomous)

module Intrinsic-BST 
        {c ℓ : Level} {A : Set c}
        {_<_ : A → A → Set ℓ}
        (<-cmp : Trichotomous _≡_ _<_) where
  
  data A↑ : Set c where
    -∞ +∞ : A↑
    ↑    : A → A↑

  data _<∞_ : A↑ → A↑ → Set ℓ where
    -∞<↑  : {x : A}           → -∞ <∞ ↑ x 
    ↑<↑   : {x y : A} → x < y → ↑ x <∞ ↑ y 
    ↑<+∞  : {x : A}           → ↑ x <∞ +∞ 
    -∞<+∞ : -∞ <∞ +∞

  open BinaryTrees using (Tri)
  open Tri

  <∞-cmp : Trichotomous _≡_ _<∞_ 
  <∞-cmp -∞ -∞ = tri≈ (λ ()) refl (λ ()) 
  <∞-cmp -∞ +∞ = tri< -∞<+∞ (λ ()) (λ ()) 
  <∞-cmp +∞ -∞ = tri> (λ ()) (λ ()) -∞<+∞ 
  <∞-cmp +∞ +∞ = tri≈ (λ ()) refl (λ ()) 
  <∞-cmp -∞ (↑ _) = tri< -∞<↑ (λ ()) (λ ()) 
  <∞-cmp +∞ (↑ _) = tri> (λ ()) (λ ()) ↑<+∞ 
  <∞-cmp (↑ _) -∞ = tri> (λ ()) (λ ()) -∞<↑ 
  <∞-cmp (↑ _) +∞ = tri< ↑<+∞ (λ ()) (λ ())
  <∞-cmp (↑ x) (↑ y) 
    with <-cmp x y
  ... | tri< x<y ¬x=y ¬y<x =
          tri<
            (↑<↑ x<y)
            (λ { refl → ¬y<x x<y })
            λ { (↑<↑ y<x) → ¬y<x y<x }
  ... | tri≈ ¬x<x refl _ =
          tri≈
            (λ { (↑<↑ x<x) → ¬x<x x<x })
            refl
            λ { (↑<↑ x<x) → ¬x<x x<x }
  ... | tri> ¬x<y ¬x=y y<x =
          tri>
            (λ { (↑<↑ x<y) → ¬x<y x<y })
            (λ { refl → ¬x=y refl })
            (↑<↑ y<x)

  open module Impl = Intrinsic-BST-Impl _<∞_ 
    hiding (BST; insert)

  BST : Set (c ⊔ ℓ)
  BST = Impl.BST -∞ +∞

  insert : (a : A) → BST → BST
  insert a t = Impl.insert <∞-cmp (↑ a) -∞<↑ ↑<+∞ t

open import Data.Empty
  using (⊥; ⊥-elim)
  public

open import Relation.Nullary
  using (Dec; yes; no; ¬_)
  public

open import Relation.Unary
  using (Decidable)
  public

open import Relation.Binary.PropositionalEquality
  using (_≢_; ≢-sym)
  public

open import Relation.Binary
  using (Reflexive; Transitive; DecidableEquality)
  using (Trichotomous; Tri)
  renaming (Decidable to Decidable₂)

open import Relation.Nullary.Decidable
  renaming (map′ to map-dec)
  public

open import Data.Nat.Properties
  using (<-cmp)
  public

open BinaryTrees
  using (BinTree; empty; branch; leaf)
  public
