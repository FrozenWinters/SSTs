{-# OPTIONS --cubical #-}

module Binary where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything renaming (cong to ap) public

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)

---------------------------------------------------------------------------
-- Counting

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

∂-size : ℕ → ℕ
∂-size zero = zero
∂-size (suc n) = suc (suc (double (∂-size n)))

Δ-size : ℕ → ℕ
Δ-size n = suc (∂-size n)

---------------------------------------------------------------------------
-- Dependency Lists

data Subset : (n m : ℕ) → Type where
  done : Subset 0 0
  yes : {n m : ℕ} → Subset n m → Subset (suc n) (suc m)
  no : {n m : ℕ} → Subset n m → Subset (suc n) m

infixl 20 _∷⟨_⊚_⟩
data DepList : ℕ → Type where
  [] : DepList 0
  _∷⟨_⊚_⟩ : {n : ℕ} (l : DepList n) (m : ℕ) →
    Subset n (∂-size m) → DepList (suc n)

dep-ind-𝟙 : {n k : ℕ} →
  Subset n k → Subset (suc (double n)) (suc (double k))
dep-ind-𝟙 done = yes done
dep-ind-𝟙 (yes X) = yes (yes (dep-ind-𝟙 X))
dep-ind-𝟙 (no X) = no (no (dep-ind-𝟙 X))

dep-ind-𝟘 : {n k : ℕ} →
  Subset n k → Subset (suc (double n)) k
dep-ind-𝟘 done = no done
dep-ind-𝟘 (yes X) = no (yes (dep-ind-𝟘 X))
dep-ind-𝟘 (no X) = no (no (dep-ind-𝟘 X))

list-ind-𝟙 : {n : ℕ} → DepList n → DepList (suc (double n))
list-ind-𝟙 [] = [] ∷⟨ zero ⊚ done ⟩
list-ind-𝟙 (l ∷⟨ n ⊚ X ⟩) =
  list-ind-𝟙 l ∷⟨ n ⊚ dep-ind-𝟘 X ⟩ ∷⟨ suc n ⊚ yes (dep-ind-𝟙 X) ⟩

list-ind-𝟘 : {n : ℕ} → DepList n → DepList (double n)
list-ind-𝟘 [] = []
list-ind-𝟘 (l ∷⟨ n ⊚ X ⟩) = list-ind-𝟙 l ∷⟨ n ⊚ dep-ind-𝟘 X ⟩

Δ : (n : ℕ) → DepList (Δ-size n)
Δ zero = [] ∷⟨ zero ⊚ done ⟩
Δ (suc n) = list-ind-𝟙 (Δ n)

∂Δ : (n : ℕ) → DepList (∂-size n)
∂Δ zero = []
∂Δ (suc n) = list-ind-𝟘 (Δ n)

---------------------------------------------------------------------------
-- Ordering Of The Naturals

data _<_ : ℕ → ℕ → Type where
  n<Sn : {n : ℕ} → n < suc n
  n<Sm : {n m : ℕ} → n < m → n < suc m

Z<S : {n : ℕ} → zero < suc n
Z<S {zero} = n<Sn
Z<S {suc n} = n<Sm Z<S

S<S : {n m : ℕ} → n < m → suc n < suc m
S<S n<Sn = n<Sn
S<S (n<Sm p) = n<Sm (S<S p)

---------------------------------------------------------------------------
-- Results About Dimension

DimBounded : {n : ℕ} (k : ℕ) → DepList n → Type
DimBounded k [] = ⊤
DimBounded k (l ∷⟨ n ⊚ d ⟩) = n < k × DimBounded k l

DimBounded⁺ : {n : ℕ} (k : ℕ) → DepList n → Type
DimBounded⁺ k [] = ⊤
DimBounded⁺ k (l ∷⟨ n ⊚ d ⟩) = n < suc k × DimBounded k l

dim-ind-𝟙 : {n k : ℕ} (l : DepList n) →
  DimBounded k l → DimBounded (suc k) (list-ind-𝟙 l)
dim-ind-𝟙 [] p = Z<S , tt
dim-ind-𝟙 (l ∷⟨ n ⊚ d ⟩) (n<k , p) = S<S n<k , n<Sm n<k , dim-ind-𝟙 l p

dim-ind-𝟙⁺ : {n k : ℕ} (l : DepList n) →
  DimBounded⁺ k l → DimBounded⁺ (suc k) (list-ind-𝟙 l)
dim-ind-𝟙⁺ [] p = Z<S , tt
dim-ind-𝟙⁺ (l ∷⟨ n ⊚ d ⟩) (n<Sk , p) = S<S n<Sk , n<Sk , dim-ind-𝟙 l p

dim-ind-𝟘⁺ : {n k : ℕ} (l : DepList n) →
  DimBounded⁺ k l → DimBounded (suc k) (list-ind-𝟘 l)
dim-ind-𝟘⁺ [] p = tt
dim-ind-𝟘⁺ (l ∷⟨ n ⊚ d ⟩) (n<Sk , p) = n<Sk , dim-ind-𝟙 l p

Δ-dim : (n : ℕ) → DimBounded⁺ n (Δ n)
Δ-dim zero = n<Sn , tt
Δ-dim (suc n) = dim-ind-𝟙⁺ (Δ n) (Δ-dim n)

∂-dim : (n : ℕ) → DimBounded n (∂Δ n)
∂-dim zero = tt
∂-dim (suc n) = dim-ind-𝟘⁺ (Δ n) (Δ-dim n)

---------------------------------------------------------------------------
-- Transitivity

data _≤_ : {n k l : ℕ} → Subset n k → Subset n l → Type where
  none : done ≤ done
  yy : {n k l : ℕ} {S : Subset n k} {T : Subset n l} → S ≤ T → yes S ≤ yes T
  ny : {n k l : ℕ} {S : Subset n k} {T : Subset n l} → S ≤ T → no S ≤ yes T
  nn : {n k l : ℕ} {S : Subset n k} {T : Subset n l} → S ≤ T → no S ≤ no T

TransStep : {n k : ℕ} (l : DepList n) → Subset n k → Type
TransStep l done = ⊤
TransStep (l ∷⟨ n ⊚ Y ⟩) (yes X) = Y ≤ X × TransStep l X
TransStep (l ∷⟨ n ⊚ Y ⟩) (no X) = TransStep l X

Transitive : {n : ℕ} → DepList n → Type
Transitive [] = ⊤
Transitive (l ∷⟨ n ⊚ X ⟩) = TransStep l X × Transitive l

≤-ind-𝟙𝟙 : {n k l : ℕ} {S : Subset n k} {T : Subset n l} →
  S ≤ T → dep-ind-𝟙 S ≤ dep-ind-𝟙 T
≤-ind-𝟙𝟙 none = yy none
≤-ind-𝟙𝟙 (yy p) = yy (yy (≤-ind-𝟙𝟙 p))
≤-ind-𝟙𝟙 (ny p) = ny (ny (≤-ind-𝟙𝟙 p))
≤-ind-𝟙𝟙 (nn p) = nn (nn (≤-ind-𝟙𝟙 p))

≤-ind-𝟘𝟙 : {n k l : ℕ} {S : Subset n k} {T : Subset n l} →
  S ≤ T → dep-ind-𝟘 S ≤ dep-ind-𝟙 T
≤-ind-𝟘𝟙 none = ny none
≤-ind-𝟘𝟙 (yy p) = ny (yy (≤-ind-𝟘𝟙 p))
≤-ind-𝟘𝟙 (ny p) = ny (ny (≤-ind-𝟘𝟙 p))
≤-ind-𝟘𝟙 (nn p) = nn (nn (≤-ind-𝟘𝟙 p))

≤-ind-𝟘𝟘 : {n k l : ℕ} {S : Subset n k} {T : Subset n l} →
  S ≤ T → dep-ind-𝟘 S ≤ dep-ind-𝟘 T
≤-ind-𝟘𝟘 none = nn none
≤-ind-𝟘𝟘 (yy p) = nn (yy (≤-ind-𝟘𝟘 p))
≤-ind-𝟘𝟘 (ny p) = nn (ny (≤-ind-𝟘𝟘 p))
≤-ind-𝟘𝟘 (nn p) = nn (nn (≤-ind-𝟘𝟘 p))

trans-step-𝟙 : {n k : ℕ} (l : DepList n) (T : Subset n k) →
  TransStep l T → TransStep (list-ind-𝟙 l) (dep-ind-𝟙 T)
trans-step-𝟙 [] done ⋆ = none , ⋆
trans-step-𝟙 (l ∷⟨ n ⊚ Y ⟩) (yes X) (Y≤X , p) =
  yy (≤-ind-𝟙𝟙 Y≤X) , ≤-ind-𝟘𝟙 Y≤X , trans-step-𝟙 l X p
trans-step-𝟙 (l ∷⟨ n ⊚ Y ⟩) (no X) p = trans-step-𝟙 l X p

trans-step-𝟘 : {n k : ℕ} (l : DepList n) (d : Subset n k) →
  TransStep l d → TransStep (list-ind-𝟙 l) (dep-ind-𝟘 d)
trans-step-𝟘 [] done ⋆ = ⋆
trans-step-𝟘 (l ∷⟨ n ⊚ Y ⟩) (yes X) (Y≤X , p) =
   ≤-ind-𝟘𝟘 Y≤X , trans-step-𝟘 l X p
trans-step-𝟘 (l ∷⟨ n ⊚ Y ⟩) (no X) p = trans-step-𝟘 l X p

≤-refl : {n k : ℕ} (X : Subset n k) → X ≤ X
≤-refl done = none
≤-refl (yes d) = yy (≤-refl d)
≤-refl (no d) = nn (≤-refl d)

trans-ind-𝟙 : {n : ℕ} (l : DepList n) →
  Transitive l → Transitive (list-ind-𝟙 l)
trans-ind-𝟙 [] ⋆ = tt , tt
trans-ind-𝟙 (l ∷⟨ n ⊚ X ⟩) (p , q) =
  (≤-ind-𝟘𝟙 (≤-refl X) , trans-step-𝟙 l X p) , trans-step-𝟘 l X p , trans-ind-𝟙 l q

trans-ind-𝟘 : {n : ℕ} (l : DepList n) →
  Transitive l → Transitive (list-ind-𝟘 l)
trans-ind-𝟘 [] ⋆ = tt
trans-ind-𝟘 (l ∷⟨ n ⊚ X ⟩) (p , q) =
  trans-step-𝟘 l X p , trans-ind-𝟙 l q

Δ-trans : (n : ℕ) → Transitive (Δ n)
Δ-trans zero = tt , tt
Δ-trans (suc n) = trans-ind-𝟙 (Δ n) (Δ-trans n)

∂-trans : (n : ℕ) → Transitive (∂Δ n)
∂-trans zero = tt
∂-trans (suc n) = trans-ind-𝟘 (Δ n) (Δ-trans n)

---------------------------------------------------------------------------
-- Thinnings

thin : {n k : ℕ} (l : DepList n) (X : Subset n k) (p : TransStep l X) → DepList k
thin-dep : {n k l : ℕ} {X : Subset n k} {Y : Subset n l} → Y ≤ X → Subset k l

thin [] done ⋆ = []
thin (l ∷⟨ n ⊚ Y ⟩) (yes X) (Y≤X , 𝓉) = thin l X 𝓉 ∷⟨ n ⊚ thin-dep Y≤X ⟩
thin (l ∷⟨ n ⊚ Y ⟩) (no X) 𝓉 = thin l X 𝓉

thin-dep none = done
thin-dep (yy p) = yes (thin-dep p)
thin-dep (ny p) = no (thin-dep p)
thin-dep (nn p) = thin-dep p

thin-dep-𝟘𝟘 : {n k m : ℕ} {X : Subset n k} {Y : Subset n m} (Y≤X : Y ≤ X) →
  thin-dep (≤-ind-𝟘𝟘 Y≤X) ≡ thin-dep Y≤X
thin-dep-𝟘𝟘 none = refl
thin-dep-𝟘𝟘 (yy Y≤X) i = yes (thin-dep-𝟘𝟘 Y≤X i)
thin-dep-𝟘𝟘 (ny Y≤X) i = no (thin-dep-𝟘𝟘 Y≤X i)
thin-dep-𝟘𝟘 (nn Y≤X) = thin-dep-𝟘𝟘 Y≤X

thin-dep-𝟘𝟙 : {n k m : ℕ} {X : Subset n k} {Y : Subset n m} (Y≤X : Y ≤ X) →
  thin-dep (≤-ind-𝟘𝟙 Y≤X) ≡ dep-ind-𝟘 (thin-dep Y≤X)
thin-dep-𝟘𝟙 none = refl
thin-dep-𝟘𝟙 (yy Y≤X) i = no (yes (thin-dep-𝟘𝟙 Y≤X i))
thin-dep-𝟘𝟙 (ny Y≤X) i = no (no (thin-dep-𝟘𝟙 Y≤X i))
thin-dep-𝟘𝟙 (nn Y≤X) = thin-dep-𝟘𝟙 Y≤X

thin-dep-𝟙𝟙 : {n k m : ℕ} {X : Subset n k} {Y : Subset n m} (Y≤X : Y ≤ X) →
  thin-dep (≤-ind-𝟙𝟙 Y≤X) ≡ dep-ind-𝟙 (thin-dep Y≤X)
thin-dep-𝟙𝟙 none = refl
thin-dep-𝟙𝟙 (yy Y≤X) i = yes (yes (thin-dep-𝟙𝟙 Y≤X i))
thin-dep-𝟙𝟙 (ny Y≤X) i = no (no (thin-dep-𝟙𝟙 Y≤X i))
thin-dep-𝟙𝟙 (nn Y≤X) = thin-dep-𝟙𝟙 Y≤X

thin-𝟘 : {n k : ℕ} (l : DepList n) (X : Subset n k) (𝓉 : TransStep l X) →
  thin (list-ind-𝟙 l) (dep-ind-𝟘 X) (trans-step-𝟘 l X 𝓉) ≡ thin l X 𝓉
thin-𝟘 [] done 𝓉 = refl
thin-𝟘 (l ∷⟨ n ⊚ Y ⟩) (yes X) (Y≤X , 𝓉) i =
  thin-𝟘 l X 𝓉 i ∷⟨ n ⊚ thin-dep-𝟘𝟘 Y≤X i ⟩
thin-𝟘 (l ∷⟨ n ⊚ Y ⟩) (no X) 𝓉 = thin-𝟘 l X 𝓉

thin-𝟙 : {n k : ℕ} (l : DepList n) (X : Subset n k) (𝓉 : TransStep l X) →
  thin (list-ind-𝟙 l) (dep-ind-𝟙 X) (trans-step-𝟙 l X 𝓉) ≡ list-ind-𝟙 (thin l X 𝓉)
thin-𝟙 [] done 𝓉 = refl
thin-𝟙 (l ∷⟨ n ⊚ Y ⟩) (yes X) (Y≤X , 𝓉) i =
  thin-𝟙 l X 𝓉 i ∷⟨ n ⊚ thin-dep-𝟘𝟙 Y≤X i ⟩ ∷⟨ suc n ⊚ yes (thin-dep-𝟙𝟙 Y≤X i) ⟩
thin-𝟙 (l ∷⟨ n ⊚ Y ⟩) (no X) 𝓉 = thin-𝟙 l X 𝓉

---------------------------------------------------------------------------
-- Results About Shape

Correct : {n : ℕ} (l : DepList n) (p : Transitive l) → Type
Correct [] ⋆ = ⊤
Correct (l ∷⟨ n ⊚ X ⟩) (𝓉 , p) = (thin l X 𝓉  ≡ ∂Δ n) × Correct l p

all-yes : (n : ℕ) → Subset n n
all-yes zero = done
all-yes (suc n) = yes (all-yes n)

yes-lem : (n : ℕ) → dep-ind-𝟙 (all-yes n) ≡ all-yes (suc (double n))
yes-lem zero = refl
yes-lem (suc n) i = yes (yes (yes-lem n i))

thin-refl : {n k : ℕ} (X : Subset n k) → thin-dep (≤-refl X) ≡ all-yes k
thin-refl done = refl
thin-refl (yes X) i = yes (thin-refl X i)
thin-refl (no X) = thin-refl X

Δ-lem : (n : ℕ) → Δ n ≡ ∂Δ n ∷⟨ n ⊚ all-yes (∂-size n) ⟩
Δ-lem zero = refl
Δ-lem (suc n) =
  list-ind-𝟙 (Δ n)
    ≡⟨ ap list-ind-𝟙 (Δ-lem n) ⟩
  list-ind-𝟘 (∂Δ n ∷⟨ n ⊚ all-yes (∂-size n) ⟩)
    ∷⟨ suc n ⊚ yes (dep-ind-𝟙 (all-yes (∂-size n))) ⟩
    ≡⟨ (λ i → list-ind-𝟘 (Δ-lem n (~ i)) ∷⟨ suc n ⊚ yes (yes-lem (∂-size n) i) ⟩) ⟩
  ∂Δ (suc n) ∷⟨ suc n ⊚ all-yes (∂-size (suc n)) ⟩
    ∎

shape-ind-𝟙 : {n : ℕ} (l : DepList n) (p : Transitive l) →
  Correct l p → Correct (list-ind-𝟙 l) (trans-ind-𝟙 l p)
shape-ind-𝟙 [] p q = refl , tt
shape-ind-𝟙 (l ∷⟨ n ⊚ X ⟩) (𝓉 , p) (𝓈 , q) =
  (thin (list-ind-𝟙 l) (dep-ind-𝟙 X) (trans-step-𝟙 l X 𝓉)
    ∷⟨ n ⊚ thin-dep (≤-ind-𝟘𝟙 (≤-refl X)) ⟩
    ≡⟨ (λ i → thin-𝟙 l X 𝓉 i ∷⟨ n ⊚ thin-dep-𝟘𝟙 (≤-refl X) i ⟩) ⟩
  list-ind-𝟙 (thin l X 𝓉) ∷⟨ n ⊚ dep-ind-𝟘 (thin-dep (≤-refl X)) ⟩
    ≡⟨ (λ i → list-ind-𝟙 (𝓈 i) ∷⟨ n ⊚ dep-ind-𝟘 (thin-refl X i) ⟩) ⟩
  list-ind-𝟘 (∂Δ n ∷⟨ n ⊚ all-yes (∂-size n) ⟩)
    ≡⟨ (λ i → list-ind-𝟘 (Δ-lem n (~ i))) ⟩
  list-ind-𝟘 (Δ n)
    ∎) ,
  thin-𝟘 l X 𝓉 ∙ 𝓈 ,
  shape-ind-𝟙 l p q

shape-ind-𝟘 : {n : ℕ} (l : DepList n) (p : Transitive l) →
  Correct l p → Correct (list-ind-𝟘 l) (trans-ind-𝟘 l p)
shape-ind-𝟘 [] p q = tt
shape-ind-𝟘 (l ∷⟨ n ⊚ X ⟩) (𝓉 , p) (𝓈 , q) =
  thin-𝟘 l X 𝓉 ∙ 𝓈 , shape-ind-𝟙 l p q

Δ-shape : (n : ℕ) → Correct (Δ n) (Δ-trans n)
Δ-shape zero = refl , tt
Δ-shape (suc n) = shape-ind-𝟙 (Δ n) (Δ-trans n) (Δ-shape n)

∂-shape : (n : ℕ) → Correct (∂Δ n) (∂-trans n)
∂-shape zero = tt
∂-shape (suc n) = shape-ind-𝟘 (Δ n) (Δ-trans n) (Δ-shape n)


