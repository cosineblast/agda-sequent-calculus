
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

-- TODO: Explicit Weaking, Explicit Contraction, Cut

-- Examples:

s : {A B C : Set} → [] ⊢ [ (A Implies B Implies C) Implies (A Implies B) Implies A Implies C ]
s = R→ (R→ (R→ (LE 1 (L→ I (LE 2 (L→ (LE 1 I) (L→ I I)))))))

k : {A B : Set} → [] ⊢ [ A Implies (B Implies A) ]
k = R→ (R→ (LE 1 I))

i : {A : Set} → [] ⊢ [ A Implies A ]
i = R→ I

decurry : { A B C : Set } → [ A Implies B Implies C ] ⊢ [ (A And B) Implies C ]
decurry = R→ (L∧ (LE 2 (L→ I (L→ (LE 1 I) I))))

dem1 : {A B : Set} → [ Not (A Or B) ] ⊢ [ Not A And Not B ]
dem1 = L¬ (R∨ (RE 2 (R∧ (R¬ I) (R¬ (RE 1 I)))))

dem2 : {A B : Set} → [ Not A And Not B ] ⊢ [ Not (A Or B) ]
dem2 = L∧ (R¬ (L∨ (LE 1 (L¬ I)) (LE 2 (L¬ I))))

dem3 : {A B : Set} → [ Not A Or Not B ] ⊢ [ Not (A And B) ]
dem3 = R¬ (L∧ (LE 2 (L∨ (L¬ I) (L¬ (LE 1 I)))))

tnd : {A : Set} → [] ⊢ [ A Or (Not A) ]
tnd = R∨ (RE 1 (R¬ I))

dne : {A : Set} → [ Not (Not A) ] ⊢ [ A ]
dne = L¬ (R¬ I)

dem4 : {A B : Set} → [ Not (A And B) ] ⊢ [  Not A Or Not B ]
dem4 = R∨ (L¬ (R∧ (RE 1 (R¬ I)) (RE 2 (R¬ I))))

