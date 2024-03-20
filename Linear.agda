
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Data.List
open import Data.Bool
open import Agda.Primitive
open import Data.Product using (_×_ ; _,_; proj₁; proj₂)

data _And_ (A : Set) (B : Set) : Set where
data _Or_ (A : Set) (B : Set) : Set where
data _Times_ (A : Set) (B : Set) : Set where
data _Plus_ (A : Set) (B : Set) : Set where

data Not (A : Set) : Set where
data OfCourse (A : Set) : Set where
data WhyNot (A : Set) : Set where

data One : Set where
data Zero : Set where
data Top : Set where
data Bottom : Set where

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
  L× : {A B : Set} {Γ Δ : List Set} →
    ((A ∷ B ∷ Γ) ⊢ Δ) →
    ((A Times B) ∷ Γ) ⊢ Δ

  R⅋ : {A B : Set} {Γ Δ : List Set}
    → Γ ⊢ (A ∷ B ∷ Δ)
    → Γ ⊢ ((A Or B) ∷ Δ)

  R× : {A B : Set} {Γ Δ : List Set} (n m : Nat)
    → (take n Γ)  ⊢ (A ∷ (take m Δ)) → (drop n Γ) ⊢ (B ∷ (drop m Δ))
    → Γ ⊢ ((A Times B) ∷ Δ)

  L⅋ : {A B : Set} {Γ Δ : List Set} (n m : Nat)
    → (A ∷ take n Γ) ⊢ take m Δ → (B ∷ drop n Γ) ⊢ drop m Δ
    → ((A Or B) ∷ Γ) ⊢ Δ

  W1 : {Γ Δ : List Set} → Γ ⊢ Δ → (One ∷ Γ) ⊢ Δ
  T1 : [] ⊢ [ One ]

  W0 : {Γ Δ : List Set} → Γ ⊢ Δ → Γ ⊢ (Zero ∷ Δ)
  F0 : [ Zero ] ⊢ []

  -- Additive Rules
  L&1 : {A B : Set} {Γ Δ : List Set}
    → ((A ∷ Γ) ⊢ Δ)
    → ((A And B) ∷ Γ) ⊢ Δ

  L&2 : {A B : Set} {Γ Δ : List Set}
    → ((B ∷ Γ) ⊢ Δ)
    → ((A And B) ∷ Γ) ⊢ Δ

  R+1 : {A B : Set} {Γ Δ : List Set}
    → Γ ⊢ (A ∷ Δ)
    → Γ ⊢ ((A Plus B) ∷ Δ)

  R+2 : {A B : Set} {Γ Δ : List Set}
    → Γ ⊢ (B ∷ Δ)
    → Γ ⊢ ((A Plus B) ∷ Δ)

  R& : {A B : Set} {Γ Δ : List Set}
    → Γ ⊢ (A ∷ Δ) → Γ ⊢ (B ∷ Δ)
    → Γ ⊢ ((A And B) ∷ Δ)

  L+ : {A B : Set} {Γ Δ : List Set}
    → (A ∷ Γ) ⊢ Δ → (B ∷ Γ) ⊢ Δ
    → ((A Plus B) ∷ Γ) ⊢ Δ

  A⊥  : {Γ Δ : List Set} → (Bottom ∷ Γ) ⊢ Δ
  A⊤  : {Γ Δ : List Set} → Γ ⊢ (Top ∷ Δ)

  -- Negation Rules
  L¬ : {A : Set} {Γ Δ : List Set}
    → Γ ⊢ (A ∷ Δ)
    → (Not A ∷ Γ) ⊢ Δ

  R¬ : {A : Set} {Γ Δ : List Set}
    → (A ∷ Γ) ⊢ Δ
    → Γ ⊢ (Not A ∷ Δ)

  -- Exponential Rules
  R! : {A : Set} {Γ Δ : List Set}
    → (map OfCourse Γ) ⊢ (A ∷ (map WhyNot Δ))
    → (map OfCourse Γ) ⊢ (OfCourse A ∷ (map WhyNot Δ))

  W! : {A : Set} {Γ Δ : List Set}
    → Γ ⊢ Δ
    → (OfCourse A ∷ Γ) ⊢ Δ

  C! : {A : Set} {Γ Δ : List Set}
    → (OfCourse A ∷ OfCourse A ∷ Γ) ⊢ Δ
    → (OfCourse A ∷ Γ) ⊢ Δ

  D! : {A : Set} {Γ Δ : List Set}
    → (A ∷ Γ) ⊢ Δ
    → (OfCourse A ∷ Γ) ⊢ Δ

  L? : {A : Set} {Γ Δ : List Set}
    → (A ∷ (map OfCourse Γ)) ⊢ (map WhyNot Δ)
    → (WhyNot A ∷ (map OfCourse Γ)) ⊢ (map WhyNot Δ)

  W? : {A : Set} {Γ Δ : List Set}
    → Γ ⊢ Δ
    → Γ ⊢ (WhyNot A ∷ Δ)

  C? : {A : Set} {Γ Δ : List Set}
    → Γ ⊢ (WhyNot A ∷ WhyNot A ∷ Δ)
    → Γ ⊢ (WhyNot A ∷ Δ)

  D? : {A : Set} {Γ Δ : List Set}
    → Γ ⊢ (A ∷ Δ)
    → Γ ⊢ (WhyNot A ∷ Δ)

  -- Exchange Rule
  LE : {A B : Set} {Γ Δ : List Set}
    → (n : Nat)
    → (pick n Γ) ⊢ Δ → Γ ⊢ Δ

  RE : {A B : Set} {Γ Δ : List Set}
    → (n : Nat)
    → Γ ⊢ (pick n Δ) → Γ ⊢ Δ

-- Examples:

-- Linear Implication

_⊸_ : Set → Set → Set
A ⊸ B = (Not A) Or B
infixr 20 _⊸_

R⊸ : {A B : Set} {Γ Δ : List Set} → (A ∷ Γ) ⊢ (B ∷ Δ) → Γ ⊢ ((A ⊸ B) ∷ Δ)
R⊸ p = R⅋ (R¬ p)

L⊸ : {A B : Set} {Γ Δ : List Set} (n m : Nat) → (Not A ∷ take n Γ) ⊢ take m Δ → (B ∷ drop n Γ) ⊢ drop m Δ → ((A ⊸ B) ∷ Γ) ⊢ Δ
L⊸ n m p1 p2 = L⅋ n m p1 p2


modpon : {A B : Set} → (A ⊸ B ∷ A ∷ []) ⊢ [ B ]
modpon = L⊸ 1 0 (L¬ I) I

com× : {A B : Set} → [] ⊢ [(A Times B) ⊸ (B Times A)]
com× = R⊸ (L× (LE 1 (R× 1 0 I I)))

I× : {A B : Set} → [] ⊢ [ A ⊸ B ⊸ (A Times B) ]
I× = R⊸ (R⊸ (LE 1 (R× 1 0 I I)))

fst& : {A B : Set} → [ A And B ] ⊢ [ A ]
fst& = L&1 I

snd& : {A B : Set} → [ A And B ] ⊢ [ B ]
snd& = L&2 I

left+ : {A B : Set} → [ A ] ⊢ [ A Plus B ]
left+ = R+1 I

right+ : {A B : Set} → [ B ] ⊢ [ A Plus B ]
right+ = R+2 I

match+ : {A B C : Set} → (A Plus B ∷ ((A ⊸ C) And (B ⊸ C)) ∷ []) ⊢ [ C ]
match+ = L+ (LE 1 (L&1 modpon)) (LE 1 (L&2 modpon))

-- Remarkable Formulas from Wikipedia
_⟛_ : List Set → List Set → Set₁
x ⟛ y = (x ⊢ y) × (y ⊢ x)

dist×+l : {A B C : Set} → [ A Times (B Plus C) ] ⟛ [ (A Times B) Plus (A Times C) ]
dist×+l =
  L× (LE 1 (L+ (LE 1 (R+1 (R× 1 0 I I))) (R+2 (LE 1 (R× 1 0 I I)))))
  ,
  L+ (L× (R× 1 0 I (R+1 I))) (L× (R× 1 0 I (R+2 I)))

dist⅋&l : {A B C : Set} → [ A Or (B And C) ] ⟛ [ (A Or B) And (A Or C) ]
dist⅋&l =
  R& (R⅋ (L⅋ 0 1 I (L&1 I))) (R⅋ (L⅋ 0 1 I (L&2 I)))
  ,
  R⅋ (RE 1 (R& (L&1 (RE 1 (L⅋ 0 1 I I))) (L&2 (RE 1 (L⅋ 0 1 I I)))))

dist⊸&l : {A B C : Set} → [ A ⊸ (B And C) ] ⟛ [ (A ⊸ B) And (A ⊸ C) ]
dist⊸&l = (proj₁ dist⅋&l) , (proj₂ dist⅋&l)



-- could use cut
law-!&× : {A B : Set} → [ OfCourse (A And B) ] ⟛ [ (OfCourse A) Times (OfCourse B) ]
law-!&× =
  C! (R× 1 0 (R! (D! (L&1 I))) (R! (D! (L&2 I))))
  ,
  L× (R! (R& (LE 1 (W! (D! I))) (W! (D! I))))

law-?+⅋ : {A B : Set} → [ WhyNot (A Plus B) ] ⟛ [ (WhyNot A) Or (WhyNot B) ]
law-?+⅋ =
  R⅋ (L? (L+ (RE 1 (W? (D? I))) (W? (D? I))))
  ,
  C? (L⅋ 0 1 (L? (D? (R+1 I))) (L? (D? (R+2 I))))

law-n?!n : {A : Set} → [ Not (WhyNot A) ] ⟛ [ OfCourse (Not A) ]
law-n?!n =
  L¬ (RE 1 (R! (R¬ (D? I))))
  ,
  R¬ (L? (LE 1 (D! (L¬ I))))


-- A, Not A -o 1 |- A v A

what : {A : Set} →  (A ∷ [ Not A ⊸ One ])  ⊢ [ A Or A ]
what = LE 1 (R⅋ (L⊸ 0 1 (L¬ (R¬ I)) (W1 I)))




