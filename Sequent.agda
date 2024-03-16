
module Sequent where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Primitive

open import Data.Product

open import Data.List

-- Pick function: Given a List A and n, returns a list
-- with the elements of A, but the element at index got moved
-- to its start. If n >= len(A), picks the last element

-- This is important to allow for a nice exchange rule definition

pick : { l : Level }{ A : Set l } → Nat → List A → List A
pick 0 xs = xs
pick _ [] = []
pick (suc n) (x ∷ xs) with pick n xs
... | [] = x ∷ xs
... | (t ∷ ts) = t ∷ x ∷ ts

data _And_ (A : Set) (B : Set) : Set where
data _Or_ (A : Set) (B : Set) : Set where
data _Implies_ (A : Set) (B : Set) : Set where
data Not (A : Set) : Set where

infixr 20 _Implies_

data _⊢_ : List Set → List Set → Set1 where
  I : {A : Set} {Γ Δ : List Set} → (A ∷ Γ) ⊢ (A ∷ Δ)
  L∧ : {A B : Set} {Γ Δ : List Set} → (A ∷ B ∷ Γ) ⊢ Δ → ((A And B) ∷ Γ) ⊢ Δ
  R∨ : {A B : Set} {Γ Δ : List Set} → Δ ⊢ (A ∷ B ∷ Γ) → Δ ⊢ (A Or B ∷ Γ)

  L∨ : {A B : Set} {Γ Δ : List Set} → (A ∷ Γ) ⊢ Δ → (B ∷ Γ) ⊢ Δ  → (A Or B ∷ Γ) ⊢ Δ
  R∧ : {A B : Set} {Γ Δ : List Set} → Γ ⊢ (A ∷ Δ) → Γ ⊢ (B ∷ Δ) → Γ ⊢ (A And B ∷ Δ)

  R→ : {A B : Set} {Γ Δ : List Set} → (A ∷ Γ) ⊢ (B ∷ Δ) → Γ ⊢ (A Implies B ∷ Δ)
  L→ : {A B : Set} {Γ Δ : List Set} → Γ ⊢ (A ∷ Δ) → (B ∷ Γ) ⊢ Δ  → (A Implies B ∷ Γ) ⊢ Δ

  L¬ : {A : Set} {Γ Δ : List Set} → Γ ⊢ (A ∷ Δ) → (Not A ∷ Γ) ⊢ Δ
  R¬ : {A : Set} {Γ Δ : List Set} → (A ∷ Γ) ⊢ Δ → Γ ⊢ (Not A ∷ Δ)

  CL : {A : Set} {Γ Δ : List Set} → (A ∷ A ∷ Γ) ⊢ Δ → (A ∷ Γ) ⊢ Δ
  CR : {A : Set} {Γ Δ : List Set} → Γ ⊢ (A ∷ A ∷ Δ) → Γ ⊢ (A ∷ Δ)

  LE : {A B : Set} {Γ Δ : List Set} → (n : Nat) → (pick n Γ) ⊢ Δ → Γ ⊢ Δ
  RE : {A B : Set} {Γ Δ : List Set} → (n : Nat) → Γ ⊢ (pick n Δ) → Γ ⊢ Δ











