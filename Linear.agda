
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Data.List
open import Data.Bool
open import Agda.Primitive

data _And_ (A : Set) (B : Set) : Set where
data _Or_ (A : Set) (B : Set) : Set where
data _Times_ (A : Set) (B : Set) : Set where
data _Plus_ (A : Set) (B : Set) : Set where

data Not (A : Set) : Set where
data OfCourse (A : Set) : Set where
data WhyNot (A : Set) : Set where

-- with the elements of A, but the element at index got moved
-- to its start. If n >= len(A), picks the last element

-- This is important to allow for a nice exchange rule definition

pick : { l : Level }{ A : Set l } → Nat → List A → List A
pick 0 xs = xs
pick _ [] = []
pick (suc n) (x ∷ xs) with pick n xs
... | [] = x ∷ xs
... | (t ∷ ts) = t ∷ x ∷ ts

data _⊢_ : List Set → List Set → Set₁ where

  -- Identity Axiom
  I : {A : Set} → [ A ] ⊢ [ A ]

  -- Multiplicative Rules
  L× : {A B : Set} {Γ Δ : List Set} → ((A ∷ B ∷ Γ) ⊢ Δ) → ((A Times B) ∷ Γ) ⊢ Δ
  R⅋ : {A B : Set} {Γ Δ : List Set} → Γ ⊢ (A ∷ B ∷ Δ) → Γ ⊢ ((A Or B) ∷ Δ)

  R× : {A B : Set} {Γ Δ : List Set} (n m : Nat) → (take n Γ)  ⊢ (A ∷ (take m Δ)) → (drop n Γ) ⊢ (B ∷ (drop m Δ)) → Γ ⊢ ((A Times B) ∷ Δ)
  L⅋ : {A B : Set} {Γ Δ : List Set} (n m : Nat) → (A ∷ take n Γ) ⊢ take m Δ → (B ∷ drop n Γ) ⊢ drop m Δ → ((A Or B) ∷ Γ) ⊢ Δ

  -- Additive Rules
  L&1 : {A B : Set} {Γ Δ : List Set} → ((A ∷ Γ) ⊢ Δ) → ((A And B) ∷ Γ) ⊢ Δ
  L&2 : {A B : Set} {Γ Δ : List Set} → ((B ∷ Γ) ⊢ Δ) → ((A And B) ∷ Γ) ⊢ Δ
  R+1 : {A B : Set} {Γ Δ : List Set} → Γ ⊢ (A ∷ Δ) → Γ ⊢ ((A Plus B) ∷ Δ)
  R+2 : {A B : Set} {Γ Δ : List Set} → Γ ⊢ (B ∷ Δ) → Γ ⊢ ((A Plus B) ∷ Δ)

  R& : {A B : Set} {Γ Δ : List Set} → Γ ⊢ (A ∷ Δ) → Γ ⊢ (B ∷ Δ) → Γ ⊢ ((A And B) ∷ Δ)
  L+ : {A B : Set} {Γ Δ : List Set} → (A ∷ Γ) ⊢ Δ → (B ∷ Γ) ⊢ Δ → ((A Plus B) ∷ Γ) ⊢ Δ

  -- Negation Rules
  L¬ : {A : Set} {Γ Δ : List Set} → Γ ⊢ (A ∷ Δ) → (Not A ∷ Γ) ⊢ Δ
  R¬ : {A : Set} {Γ Δ : List Set} → (A ∷ Γ) ⊢ Δ → Γ ⊢ (Not A ∷ Δ)

  -- Exponential Rules
  R! : {A : Set} {Γ Δ : List Set} → (map OfCourse Γ) ⊢ (A ∷ (map WhyNot Δ)) → (map OfCourse Γ) ⊢ (OfCourse A ∷ (map WhyNot Δ))
  W! : {A : Set} {Γ Δ : List Set} → Γ ⊢ Δ → (OfCourse A ∷ Γ) ⊢ Δ
  C! : {A : Set} {Γ Δ : List Set} → (OfCourse A ∷ OfCourse A ∷ Γ) ⊢ Δ → (OfCourse A ∷ Γ) ⊢ Δ
  D! : {A : Set} {Γ Δ : List Set} → (A ∷ Γ) ⊢ Δ → (OfCourse A ∷ Γ) ⊢ Δ

  L? : {A : Set} {Γ Δ : List Set} → (A ∷ (map OfCourse Γ)) ⊢ (map WhyNot Δ) → (WhyNot A ∷ (map OfCourse Γ)) ⊢ (map WhyNot Δ)
  W? : {A : Set} {Γ Δ : List Set} → Γ ⊢ Δ → Γ ⊢ (WhyNot A ∷ Δ)
  C? : {A : Set} {Γ Δ : List Set} → Γ ⊢ (WhyNot A ∷ WhyNot A ∷ Δ) → Γ ⊢ (WhyNot A ∷ Δ)
  D? : {A : Set} {Γ Δ : List Set} → Γ ⊢ (A ∷ Δ) → Γ ⊢ (WhyNot A ∷ Δ)

  -- Exchange Rule
  LE : {A B : Set} {Γ Δ : List Set} → (n : Nat) → (pick n Γ) ⊢ Δ → Γ ⊢ Δ
  RE : {A B : Set} {Γ Δ : List Set} → (n : Nat) → Γ ⊢ (pick n Δ) → Γ ⊢ Δ


-- Examples

