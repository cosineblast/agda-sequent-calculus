
module Sequent where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Primitive

open import Data.Product

open import Data.List

data _And_ (A : Set) (B : Set) : Set where
data _Or_ (A : Set) (B : Set) : Set where
data _Implies_ (A : Set) (B : Set) : Set where
data Not (A : Set) : Set where

data _⊢_ : List Set → List Set → Set1 where
  I : {A : Set} {Γ Δ : List Set} → (Γ ++ [ A ]) ⊢ (Δ ++ [ A ])
  L∧ : {A B : Set} {Γ Δ : List Set} → (Γ ++ (A ∷ B ∷ [])) ⊢ Δ → (Γ ++ [ A And B ]) ⊢ Δ
  R∨ : {A B : Set} {Γ Δ : List Set} → Δ ⊢ (Γ ++ [ A Or B ]) → Δ ⊢ (Γ ++ (A ∷ B ∷ []))

  L∨ : {A B : Set} {Γ Δ : List Set} → (Γ ++ [ A ]) ⊢ Δ → (Γ ++ [ B ]) ⊢ Δ  → (Γ ++ [ A Or B ]) ⊢ Δ
  R∧ : {A B : Set} {Γ Δ : List Set} → Γ ⊢ (Δ ++ [ A ]) → Γ ⊢ (Δ ++ [ B ]) → Γ ⊢ (Δ ++ [ A And B ])

  R→ : {A B : Set} {Γ Δ : List Set} → (Γ ++ [ A ]) ⊢ (Δ ++ [ B ]) → Γ ⊢ (Δ ++ [ A Implies B ])
  L→ : {A B : Set} {Γ Δ : List Set} → Γ ⊢ (Δ ++ [ A ]) → (Γ ++ [ B ]) ⊢ Δ  → (Γ ++ [ A Implies B ]) ⊢ Δ

  L¬ : {A : Set} {Γ Δ : List Set} → (Γ ++ [ A ]) ⊢ Δ → Γ ⊢ (Not A ∷ Δ)
  R¬ : {A : Set} {Γ Δ : List Set} → Γ ⊢ (Δ ++ [ A ]) → (Γ ++ [ Not A ]) ⊢ Δ













