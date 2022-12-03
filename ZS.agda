{-# OPTIONS --cubical --guardedness --rewriting #-}

module ZS where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything renaming (cong to ap) public

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

{-# BUILTIN REWRITE _≡_ #-}

---------------------------------------------------------------------------
-- Type Structures

record TyStr ℓ : Type (lsuc ℓ) where
  coinductive
  field
    𝑡𝑦 : Type ℓ
    𝑒𝑥 : 𝑡𝑦 → TyStr ℓ

open TyStr public

record TyMor (𝒯 : TyStr ℓ₁) (𝒮 : TyStr ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    𝑓𝑢𝑛 : 𝑡𝑦 𝒯 → 𝑡𝑦 𝒮
    𝑢𝑝 : (A : 𝑡𝑦 𝒯) → TyMor (𝑒𝑥 𝒯 A) (𝑒𝑥 𝒮 (𝑓𝑢𝑛 A))

open TyMor public

idTyMor : (𝒯 : TyStr ℓ) → TyMor 𝒯 𝒯
𝑓𝑢𝑛 (idTyMor 𝒯) A = A
𝑢𝑝 (idTyMor 𝒯) A = idTyMor (𝑒𝑥 𝒯 A)

infixl 20 _∘TyMor_
_∘TyMor_ : {𝒯 : TyStr ℓ₁} {𝒮 : TyStr ℓ₂} {ℒ : TyStr ℓ₃} →
  TyMor 𝒮 ℒ → TyMor 𝒯 𝒮 → TyMor 𝒯 ℒ
𝑓𝑢𝑛 (𝑓 ∘TyMor 𝑔) = 𝑓𝑢𝑛 𝑓 ∘ 𝑓𝑢𝑛 𝑔
𝑢𝑝 (𝑓 ∘TyMor 𝑔) A = 𝑢𝑝 𝑓 (𝑓𝑢𝑛 𝑔 A) ∘TyMor 𝑢𝑝 𝑔 A

idR : {𝒯₁ : TyStr ℓ₁} {𝒯₂ : TyStr ℓ₂} (𝑓 : TyMor 𝒯₁ 𝒯₂) →
  𝑓 ∘TyMor idTyMor 𝒯₁ ≡ 𝑓
𝑓𝑢𝑛 (idR 𝑓 i) A = 𝑓𝑢𝑛 𝑓 A
𝑢𝑝 (idR 𝑓 i) A = idR (𝑢𝑝 𝑓 A) i

{-# REWRITE idR #-}

---------------------------------------------------------------------------
-- Wk, Z, and S Structures

record WkStr (𝒯 : TyStr ℓ) : Type ℓ where
  coinductive
  field
    𝑤𝑘 : (A : 𝑡𝑦 𝒯) → TyMor 𝒯 (𝑒𝑥 𝒯 A)
    𝑒𝑥 : (A : 𝑡𝑦 𝒯) → WkStr (𝑒𝑥 𝒯 A)

open WkStr

record ZStr (𝒯 : TyStr ℓ₁) ℓ₂ : Type (ℓ₁ ⊔ (lsuc ℓ₂)) where
  coinductive
  field
    𝑡𝑦ᶻ : 𝑡𝑦 𝒯 → Type ℓ₂
    𝑒𝑥ᶻ : {A : 𝑡𝑦 𝒯} (A' : 𝑡𝑦ᶻ A) → ZStr (𝑒𝑥 𝒯 A) ℓ₂

open ZStr

-- a SStr is a morphism of dependent TyStrs from Z to EX

record SStr {𝒯₁ : TyStr ℓ₁} {𝒯₂ : TyStr ℓ₂} (𝑓 : TyMor 𝒯₁ 𝒯₂)
  (Z : ZStr 𝒯₁ ℓ₃) (𝒲 : WkStr 𝒯₂) : Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  coinductive
  field
    𝑓𝑢𝑛ˢ : {A : 𝑡𝑦 𝒯₁} (𝓈 : 𝑡𝑦ᶻ Z A) → 𝑡𝑦 (𝑒𝑥 𝒯₂ (𝑓𝑢𝑛 𝑓 A))
    𝑢𝑝ˢ : {A : 𝑡𝑦 𝒯₁} (𝓈 : 𝑡𝑦ᶻ Z A) →
      SStr (𝑤𝑘 (𝑒𝑥 𝒲 (𝑓𝑢𝑛 𝑓 A)) (𝑓𝑢𝑛ˢ 𝓈) ∘TyMor 𝑢𝑝 𝑓 A)
        (𝑒𝑥ᶻ Z 𝓈) (𝑒𝑥 (𝑒𝑥 𝒲 (𝑓𝑢𝑛 𝑓 A)) (𝑓𝑢𝑛ˢ 𝓈))

open SStr

---------------------------------------------------------------------------
-- Contexts

data 𝐶𝑡𝑥 (𝒯 : TyStr ℓ) : ℕ → Type ℓ
𝑒𝑥𝑠 : (𝒯 : TyStr ℓ) {n : ℕ} → 𝐶𝑡𝑥 𝒯 n → TyStr ℓ

infixl 20 _⊹_
data 𝐶𝑡𝑥 𝒯 where
  ∅ : 𝐶𝑡𝑥 𝒯 0
  _⊹_ : {n : ℕ} (Γ : 𝐶𝑡𝑥 𝒯 n) → 𝑡𝑦 (𝑒𝑥𝑠 𝒯 Γ) → 𝐶𝑡𝑥 𝒯 (suc n)

π𝐶𝑡𝑥 : {𝒯 : TyStr ℓ} {n : ℕ} → 𝐶𝑡𝑥 𝒯 (suc n) → 𝐶𝑡𝑥 𝒯 n
π𝐶𝑡𝑥 (Γ ⊹ A) = Γ

𝑧𝐶𝑡𝑥 : {𝒯 : TyStr ℓ} {n : ℕ} (Γ : 𝐶𝑡𝑥 𝒯 (suc n)) → 𝑡𝑦 (𝑒𝑥𝑠 𝒯 (π𝐶𝑡𝑥 Γ))
𝑧𝐶𝑡𝑥 (Γ ⊹ A) = A

𝑒𝑥𝑠 𝒯 {n = 0} Γ = 𝒯
𝑒𝑥𝑠 𝒯 {n = suc n} Γ = 𝑒𝑥 (𝑒𝑥𝑠 𝒯 (π𝐶𝑡𝑥 Γ)) (𝑧𝐶𝑡𝑥 Γ)

𝒲-𝑒𝑥𝑠 : {𝒯 : TyStr ℓ₁} (𝒲 : WkStr 𝒯) {n : ℕ} (Γ : 𝐶𝑡𝑥 𝒯 n) →
  WkStr (𝑒𝑥𝑠 𝒯 Γ)
𝒲-𝑒𝑥𝑠 𝒲 {n = zero} Γ = 𝒲
𝒲-𝑒𝑥𝑠 𝒲 {n = suc n} Γ = 𝑒𝑥 (𝒲-𝑒𝑥𝑠 𝒲 (π𝐶𝑡𝑥 Γ)) (𝑧𝐶𝑡𝑥 Γ)

data 𝐶𝑡𝑥ᶻ {𝒯 : TyStr ℓ₁} (𝒮 : ZStr 𝒯 ℓ₂)
          : {n : ℕ} → 𝐶𝑡𝑥 𝒯 n → Type (ℓ₁ ⊔ ℓ₂)
𝑒𝑥𝑠ᶻ : {𝒯 : TyStr ℓ₁} (𝒮 : ZStr 𝒯 ℓ₂) {n : ℕ} {Γ : 𝐶𝑡𝑥 𝒯 n} →
  𝐶𝑡𝑥ᶻ 𝒮 Γ → ZStr (𝑒𝑥𝑠 𝒯 Γ) ℓ₂

data 𝐶𝑡𝑥ᶻ {𝒯 = 𝒯} 𝒮 where
  ∅ : {Γ : 𝐶𝑡𝑥 𝒯 0} → 𝐶𝑡𝑥ᶻ 𝒮 Γ
  _⊹_ : {n : ℕ} {Γ : 𝐶𝑡𝑥 𝒯 (suc n)}
    (Γ' : 𝐶𝑡𝑥ᶻ 𝒮 (π𝐶𝑡𝑥 Γ)) → 𝑡𝑦ᶻ (𝑒𝑥𝑠ᶻ 𝒮 Γ') (𝑧𝐶𝑡𝑥 Γ) → 𝐶𝑡𝑥ᶻ 𝒮 Γ

π𝐶𝑡𝑥ᶻ : {𝒯 : TyStr ℓ₁} {𝒮 : ZStr 𝒯 ℓ₂} {n : ℕ} {Γ : 𝐶𝑡𝑥 𝒯 (suc n)} →
  𝐶𝑡𝑥ᶻ 𝒮 Γ → 𝐶𝑡𝑥ᶻ 𝒮 (π𝐶𝑡𝑥 Γ)
π𝐶𝑡𝑥ᶻ (Γ' ⊹ A') = Γ'

𝑧𝐶𝑡𝑥ᶻ : {𝒯 : TyStr ℓ₁} {𝒮 : ZStr 𝒯 ℓ₂} {n : ℕ} {Γ : 𝐶𝑡𝑥 𝒯 (suc n)} →
  (Γ' : 𝐶𝑡𝑥ᶻ 𝒮 Γ) → 𝑡𝑦ᶻ (𝑒𝑥𝑠ᶻ 𝒮 (π𝐶𝑡𝑥ᶻ Γ')) (𝑧𝐶𝑡𝑥 Γ)
𝑧𝐶𝑡𝑥ᶻ (Γ' ⊹ A') = A'

𝑒𝑥𝑠ᶻ 𝒮 {n = 0} Γ' = 𝒮
𝑒𝑥𝑠ᶻ 𝒮 {n = suc n} Γ' = 𝑒𝑥ᶻ (𝑒𝑥𝑠ᶻ 𝒮 (π𝐶𝑡𝑥ᶻ Γ')) (𝑧𝐶𝑡𝑥ᶻ Γ')

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))


-- produces a context in 𝒯 from a Z-section of 𝐸𝑋 𝒯

𝑓𝑙𝑎𝑡 : {𝒯₁ : TyStr ℓ₁} {𝒯₂ : TyStr ℓ₂} {𝑓 : TyMor 𝒯₁ 𝒯₂}
  {Z : ZStr 𝒯₁ ℓ₃} {𝒲 : WkStr 𝒯₂} (𝒮 : SStr 𝑓 Z 𝒲)
  {n : ℕ} {Γ : 𝐶𝑡𝑥 𝒯₁ n} (𝓈s : 𝐶𝑡𝑥ᶻ Z Γ) → 𝐶𝑡𝑥 𝒯₂ (double n)
𝑚𝑜𝑟 : {𝒯₁ : TyStr ℓ₁} {𝒯₂ : TyStr ℓ₂} {𝑓 : TyMor 𝒯₁ 𝒯₂}
  {Z : ZStr 𝒯₁ ℓ₃} {𝒲 : WkStr 𝒯₂} (𝒮 : SStr 𝑓 Z 𝒲)
  {n : ℕ} {Γ : 𝐶𝑡𝑥 𝒯₁ n} (𝓈s : 𝐶𝑡𝑥ᶻ Z Γ) →
  TyMor (𝑒𝑥𝑠 𝒯₁ Γ) (𝑒𝑥𝑠 𝒯₂ (𝑓𝑙𝑎𝑡 𝒮 𝓈s))
𝑢𝑝𝑠ˢ : {𝒯₁ : TyStr ℓ₁} {𝒯₂ : TyStr ℓ₂} {𝑓 : TyMor 𝒯₁ 𝒯₂}
  {Z : ZStr 𝒯₁ ℓ₃} {𝒲 : WkStr 𝒯₂} (𝒮 : SStr 𝑓 Z 𝒲)
  {n : ℕ} {Γ : 𝐶𝑡𝑥 𝒯₁ n} (𝓈s : 𝐶𝑡𝑥ᶻ Z Γ) →
  SStr (𝑚𝑜𝑟 𝒮 𝓈s) (𝑒𝑥𝑠ᶻ Z 𝓈s) (𝒲-𝑒𝑥𝑠 𝒲 (𝑓𝑙𝑎𝑡 𝒮 𝓈s))

𝑓𝑙𝑎𝑡 𝒮 ∅ = ∅
𝑓𝑙𝑎𝑡 {𝑓 = 𝑓} 𝒮 {Γ = Γ ⊹ A} (𝓈s ⊹ 𝓈) =
  𝑓𝑙𝑎𝑡 𝒮 𝓈s ⊹ 𝑓𝑢𝑛 (𝑚𝑜𝑟 𝒮 𝓈s) A ⊹ 𝑓𝑢𝑛ˢ (𝑢𝑝𝑠ˢ 𝒮 𝓈s) 𝓈

𝑚𝑜𝑟 {𝑓 = 𝑓} 𝒮 ∅ = 𝑓
𝑚𝑜𝑟 {𝒲 = 𝒲} 𝒮 {Γ = Γ ⊹ A} (𝓈s ⊹ 𝓈) =
  𝑤𝑘 (𝑒𝑥 (𝒲-𝑒𝑥𝑠 𝒲 (𝑓𝑙𝑎𝑡 𝒮 𝓈s)) (𝑓𝑢𝑛 (𝑚𝑜𝑟 𝒮 𝓈s) A)) (𝑓𝑢𝑛ˢ (𝑢𝑝𝑠ˢ 𝒮 𝓈s) 𝓈)
    ∘TyMor 𝑢𝑝 (𝑚𝑜𝑟 𝒮 𝓈s) A

𝑢𝑝𝑠ˢ 𝒮 ∅ = 𝒮
𝑢𝑝𝑠ˢ 𝒮 {Γ = Γ ⊹ A} (𝓈s ⊹ 𝓈) = 𝑢𝑝ˢ (𝑢𝑝𝑠ˢ 𝒮 𝓈s) 𝓈

---------------------------------------------------------------------------
-- Indexing

data Fin : ℕ → Type where
  𝑍 : {n : ℕ} → Fin n
  𝑆 : {n : ℕ} → Fin n → Fin (suc n)

split : (n m : ℕ) → Fin (m + n)
split n zero = 𝑍
split n (suc m) = 𝑆 (split n m)

full : (n : ℕ) → Fin n
full zero = 𝑍
full (suc n) = 𝑆 (full n)

sub : (n : ℕ) → Fin n → ℕ
sub n 𝑍 = n
sub (suc n) (𝑆 m) = sub n m

shift : {n : ℕ} → Fin n → Fin (suc n)
shift 𝑍 = 𝑍
shift (𝑆 m) = 𝑆 (shift m)

sub-split : (n m : ℕ) → sub (m + n) (split n m) ≡ n
sub-split n zero = refl
sub-split n (suc m) = sub-split n m

sub-full : (n : ℕ) → sub n (full n) ≡ zero
sub-full zero = refl
sub-full (suc n) = sub-full n

sub-shift : {n : ℕ} (m : Fin n) → sub (suc n) (shift m) ≡ suc (sub n m)
sub-shift 𝑍 = refl
sub-shift (𝑆 m) = sub-shift m

{-# REWRITE sub-split sub-full sub-shift #-}

drop : {𝒯 : TyStr ℓ} {n : ℕ} (Γ : 𝐶𝑡𝑥 𝒯 n) (m : Fin n) → 𝐶𝑡𝑥 𝒯 (sub n m)
drop Γ 𝑍 = Γ
drop Γ (𝑆 m) = drop (π𝐶𝑡𝑥 Γ) m

index : {𝒯 : TyStr ℓ} {n : ℕ} (Γ : 𝐶𝑡𝑥 𝒯 (suc n)) (m : Fin n) →
  𝑡𝑦 (𝑒𝑥𝑠 𝒯 (drop Γ (𝑆 m)))
index Γ 𝑍 = 𝑧𝐶𝑡𝑥 Γ
index Γ (𝑆 m) = index (π𝐶𝑡𝑥 Γ) m

drop-full : {𝒯 : TyStr ℓ} {n : ℕ} (Γ : 𝐶𝑡𝑥 𝒯 n) →
  drop Γ (full n) ≡ ∅
drop-full ∅ = refl
drop-full (Γ ⊹ A) = drop-full Γ

index-lem : {𝒯 : TyStr ℓ} {n : ℕ} (Γ : 𝐶𝑡𝑥 𝒯 (suc n)) (m : Fin n) →
  drop Γ (shift m) ≡ drop (π𝐶𝑡𝑥 Γ) m ⊹ index Γ m
index-lem (Γ ⊹ A) 𝑍 = refl
index-lem (Γ ⊹ A) (𝑆 m) = index-lem Γ m

{-# REWRITE drop-full index-lem #-}

---------------------------------------------------------------------------
-- SSTs

-- this solves the problem of simplex extraction

module _ {𝒯 : TyStr ℓ₁} {𝒲 : WkStr 𝒯} {Z : ZStr 𝒯 ℓ₂}
         (S : SStr (idTyMor 𝒯) Z 𝒲) where

  record State : Type (ℓ₁ ⊔ ℓ₂) where
    constructor state
    field
      n : ℕ
      Γ : 𝐶𝑡𝑥 𝒯 (suc n)
      m : Fin (suc n)
      𝓈s : 𝐶𝑡𝑥ᶻ Z (drop Γ m)

  promote : State → State
  promote (state n Γ 𝑍 𝓈s) =
    state (suc (double n)) (𝑓𝑙𝑎𝑡 S 𝓈s) (full (double (suc n))) ∅
  promote (state n Γ (𝑆 m) 𝓈s) = state n Γ (𝑆 m) 𝓈s

  length : State → ℕ
  length (state n Γ 𝑍 𝓈s) = length (promote (state n Γ 𝑍 𝓈s))
  length (state n Γ (𝑆 m) 𝓈s) = sub n m

  context : (𝒮 : State) → 𝐶𝑡𝑥 𝒯 (length 𝒮)
  context (state n Γ 𝑍 𝓈s) = context (promote (state n Γ 𝑍 𝓈s))
  context (state n Γ (𝑆 m) 𝓈s) = drop Γ (𝑆 m)

  Z-context : (𝒮 : State) → 𝐶𝑡𝑥ᶻ Z (context 𝒮)
  Z-context (state n Γ 𝑍 𝓈s) = Z-context (promote (state n Γ 𝑍 𝓈s))
  Z-context (state n Γ (𝑆 m) 𝓈s) = 𝓈s

  type : (𝒮 : State) → 𝑡𝑦 (𝑒𝑥𝑠 𝒯 (context 𝒮))
  type (state n Γ 𝑍 𝓈s) = type (promote (state n Γ 𝑍 𝓈s))
  type (state n Γ (𝑆 m) 𝓈s) = index Γ m

  Req : State → Type ℓ₂
  Req 𝒮 = 𝑡𝑦ᶻ (𝑒𝑥𝑠ᶻ Z (Z-context 𝒮)) (type 𝒮)

  ex : (𝑠𝑡𝑎𝑡𝑒 : State) → Req 𝑠𝑡𝑎𝑡𝑒 → State
  ex (state n Γ 𝑍 𝓈s) 𝓈 =
    state (suc (double n)) (𝑓𝑙𝑎𝑡 S 𝓈s)
      (shift (full (suc (double n)))) (∅ ⊹ 𝓈)
  ex (state n Γ (𝑆 m) 𝓈s) 𝓈 = state n Γ (shift m) (𝓈s ⊹ 𝓈)

  Δ' : State → TyStr ℓ₂
  𝑡𝑦 (Δ' 𝑠𝑡𝑎𝑡𝑒) = Req 𝑠𝑡𝑎𝑡𝑒
  𝑒𝑥 (Δ' 𝑠𝑡𝑎𝑡𝑒) 𝓈 = Δ' (ex 𝑠𝑡𝑎𝑡𝑒 𝓈)

  Δ : {n : ℕ} (Γ : 𝐶𝑡𝑥 𝒯 (suc n)) → TyStr ℓ₂
  Δ {n = n} Γ = Δ' (state n Γ (full (suc n)) ∅)

---------------------------------------------------------------------------
-- Sing

𝒰' : (X : Type ℓ) → TyStr (lsuc ℓ)
𝑡𝑦 (𝒰' {ℓ} X) = X → Type ℓ
𝑒𝑥 (𝒰' X) A = 𝒰' (Σ X A)

𝒰 : (ℓ : Level) → TyStr (lsuc ℓ)
𝑡𝑦 (𝒰 ℓ) = Type ℓ
𝑒𝑥 (𝒰 ℓ) A = 𝒰' A

replace : {X Y : Type ℓ} (f : X → Y) → TyMor (𝒰' Y) (𝒰' X)
𝑓𝑢𝑛 (replace f) A = A ∘ f
𝑢𝑝 (replace f) A = replace (λ x → f (fst x) , snd x)

replace² : {X Y Z : Type ℓ} (f : X → Y) (g : Y → Z) →
  replace f ∘TyMor replace g ≡ replace (g ∘ f)
𝑓𝑢𝑛 (replace² f g i) A x = A (g (f x))
𝑢𝑝 (replace² f g i) A =
  replace² (λ x → f (fst x) , snd x) (λ y → g (fst y) , snd y) i

{-# REWRITE replace² #-}

𝒲-𝒰' : (X : Type ℓ) → WkStr (𝒰' X)
𝑤𝑘 (𝒲-𝒰' X) A = replace fst
𝑒𝑥 (𝒲-𝒰' X) A = 𝒲-𝒰' (Σ X A)

𝒲-𝒰 : WkStr (𝒰 ℓ)
𝑓𝑢𝑛 (𝑤𝑘 𝒲-𝒰 A) B = λ _ → B
𝑢𝑝 (𝑤𝑘 𝒲-𝒰 A) B = replace snd
𝑒𝑥 𝒲-𝒰 A = 𝒲-𝒰' A

Z' : {X : Type ℓ} → X → ZStr (𝒰' X) ℓ
𝑡𝑦ᶻ (Z' x) A = A x
𝑒𝑥ᶻ (Z' x) a = Z' (x , a)

Z : ZStr (𝒰 ℓ) ℓ
𝑡𝑦ᶻ Z A = A
𝑒𝑥ᶻ Z a = Z' a

S' : {X Y : Type ℓ} (f : X → Y) (y : Y) (p : (x : X) → y ≡ f x) →
  SStr (replace f) (Z' y) (𝒲-𝒰' X)
𝑓𝑢𝑛ˢ (S' f y p) {A} a₀ = λ {(x , a₁) → PathP (λ i → A (p x i)) a₀ a₁}
𝑢𝑝ˢ (S' f y p) {A} a =
  S' (λ x → f (fst (fst x)) , snd (fst x)) (y , a)
     (λ x i → p (fst (fst x)) i , snd x i)

S : SStr (idTyMor (𝒰 ℓ)) Z 𝒲-𝒰
𝑓𝑢𝑛ˢ S a₀ a₁ = a₀ ≡ a₁
𝑢𝑝ˢ S a = S' fst a snd

Δ-Sing : (X : Type ℓ) → TyStr ℓ
Δ-Sing X = Δ S (∅ ⊹ X)

postulate
  X : Type lzero

  x : X

  y : X
  α : x ≡ y
  
  z : X
  β : y ≡ z
  γ : x ≡ z
  𝑓₀ : PathP (λ i → x ≡ β i) α γ
    -- 𝑡𝑦 (𝑒𝑥𝑠 (Δ-Sing X) (∅ ⊹ x ⊹ y ⊹ α ⊹ z ⊹ β ⊹ γ))

  w : X
  δ : z ≡ w
  ε : y ≡ w
  𝑓₁ : PathP (λ i → y ≡ δ i) β ε
    -- 𝑡𝑦 (𝑒𝑥𝑠 (Δ-Sing X)
    --  (∅ ⊹ x ⊹ y ⊹ α ⊹ z ⊹ β ⊹ γ ⊹ 𝑓₀ ⊹ w ⊹ δ ⊹ ε))
  ζ : x ≡ w
  𝑓₂ : PathP (λ i → x ≡ δ i) γ ζ
    -- 𝑡𝑦 (𝑒𝑥𝑠 (Δ-Sing X)
    --  (∅ ⊹ x ⊹ y ⊹ α ⊹ z ⊹ β ⊹ γ ⊹ 𝑓₀ ⊹ w ⊹ δ ⊹ ε ⊹ 𝑓₁ ⊹ ζ))
  𝑓₃ : PathP (λ i → x ≡ ε i) α ζ
    -- 𝑡𝑦 (𝑒𝑥𝑠 (Δ-Sing X)
    --  (∅ ⊹ x ⊹ y ⊹ α ⊹ z ⊹ β ⊹ γ ⊹ 𝑓₀ ⊹ w ⊹ δ ⊹ ε ⊹ 𝑓₁ ⊹ ζ ⊹ 𝑓₂))
  Δ₀ : PathP (λ i → PathP (λ j → x ≡ 𝑓₁ i j) α (𝑓₂ i)) 𝑓₀ 𝑓₃
    -- 𝑡𝑦 (𝑒𝑥𝑠 (Δ-Sing X)
    --  (∅ ⊹ x ⊹ y ⊹ α ⊹ z ⊹ β ⊹ γ ⊹ 𝑓₀ ⊹ w ⊹ δ ⊹ ε ⊹ 𝑓₁ ⊹ ζ ⊹ 𝑓₂ ⊹ 𝑓₃))

well-formed =
  𝑒𝑥𝑠 (Δ-Sing X)
    (∅ ⊹ x ⊹ y ⊹ α ⊹ z ⊹ β ⊹ γ ⊹ 𝑓₀ ⊹ w ⊹ δ ⊹ ε ⊹ 𝑓₁ ⊹ ζ ⊹ 𝑓₂ ⊹ 𝑓₃ ⊹ Δ₀)
