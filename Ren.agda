{-# OPTIONS --cubical #-}

module Ren where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything renaming (cong to ap) public

open import Cubical.Data.Nat

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

data Fin : ℕ → Type where
  𝑍 : {n : ℕ} → Fin (suc n)
  𝑆 : {n : ℕ} → Fin n → Fin (suc n)

infixl 20 _⊕_
data Vec (A : Type ℓ) : ℕ → Type ℓ where
  ! : Vec A 0
  _⊕_ : {n : ℕ} → Vec A n → A → Vec A (suc n)

𝑧Vec : {A : Type ℓ} {n : ℕ} → Vec A (suc n) → A
𝑧Vec (σ ⊕ t) = t

πVec : {A : Type ℓ} {n : ℕ} → Vec A (suc n) → Vec A n
πVec (σ ⊕ t) = σ

derive : {A : Type ℓ} {n : ℕ} → Vec A n → Fin n → A
derive σ 𝑍 = 𝑧Vec σ
derive σ (𝑆 n) = derive (πVec σ) n

mapVec : {A : Type ℓ₁} {B : Type ℓ₂} {n : ℕ}
  (f : A → B) → Vec A n → Vec B n
mapVec {n = zero} f σ = !
mapVec {n = suc n} f σ = mapVec f (πVec σ) ⊕ f (𝑧Vec σ)

mapId : {A : Type ℓ} {n : ℕ} (σ : Vec A n) →
  mapVec (λ x → x) σ ≡ σ
mapId ! = refl
mapId (σ ⊕ t) = ap (_⊕ t) (mapId σ)

mapVec² : {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {n : ℕ}
  (g : B → C) (f : A → B) (σ : Vec A n) →
  mapVec g (mapVec f σ) ≡ mapVec (g ∘ f) σ
mapVec² {n = zero} g f σ = refl
mapVec² {n = suc n} g f σ i = mapVec² g f (πVec σ) i ⊕ g (f (𝑧Vec σ))

deriveMap : {A : Type ℓ₁} {B : Type ℓ₂} {n : ℕ}
  (f : A → B) (σ : Vec A n) (m : Fin n) →
  derive (mapVec f σ) m ≡ f (derive σ m)
deriveMap f σ 𝑍 = refl
deriveMap f σ (𝑆 m) = deriveMap f (πVec σ) m

Ren : ℕ → ℕ → Type
Ren n m = Vec (Fin n) m

W₁Ren : {n m : ℕ} → Ren n m → Ren (suc n) m
W₁Ren σ = mapVec 𝑆 σ

W₂Ren : {n m : ℕ} → Ren n m → Ren (suc n) (suc m)
W₂Ren σ = W₁Ren σ ⊕ 𝑍

idRen : {n : ℕ} → Ren n n
idRen {zero} = !
idRen {suc n} = W₂Ren idRen

πRen : {n : ℕ} → Ren (suc n) n
πRen = πVec idRen

deriveIdRen : {n : ℕ} (m : Fin n) → derive idRen m ≡ m
deriveIdRen 𝑍 = refl
deriveIdRen (𝑆 m) = deriveMap 𝑆 idRen m ∙ ap 𝑆 (deriveIdRen m)

_∘Ren_ : {n m k : ℕ} → Ren m k → Ren n m → Ren n k
σ ∘Ren τ = mapVec (derive τ) σ

WRenLem₀ : {n m l : ℕ} (σ : Ren m l) (τ : Ren n m) (v : Fin n) →
  W₁Ren σ ∘Ren (τ ⊕ v) ≡ σ ∘Ren τ
WRenLem₀ σ τ v = mapVec² (derive (τ ⊕ v)) 𝑆 σ

WRenLem₁ : {n m l : ℕ} (σ : Ren m l) (τ : Ren n m) →
  W₁Ren (σ ∘Ren τ) ≡ σ ∘Ren W₁Ren τ
WRenLem₁ σ τ =
  mapVec 𝑆 (mapVec (derive τ) σ)
    ≡⟨ mapVec² 𝑆 (derive τ) σ ⟩
  mapVec (𝑆 ∘ derive τ) σ
    ≡⟨ (λ i → mapVec (λ v → deriveMap 𝑆 τ v (~ i)) σ) ⟩
  mapVec (derive (mapVec 𝑆 τ)) σ
    ∎

WRenLem₂ : {n m l : ℕ} (σ : Ren m l) (τ : Ren n m) →
  W₁Ren σ ∘Ren W₂Ren τ ≡ σ ∘Ren W₁Ren τ
WRenLem₂ σ τ = WRenLem₀ σ (W₁Ren τ) 𝑍

WRenLem₃ : {n m l : ℕ} (σ : Ren m l) (τ : Ren n m) →
  W₂Ren (σ ∘Ren τ) ≡ W₂Ren σ ∘Ren W₂Ren τ
WRenLem₃ σ τ = ap (_⊕ 𝑍) (WRenLem₁ σ τ ∙ WRenLem₂ σ τ ⁻¹)

idRenL : {n m : ℕ} (σ : Ren n m) → idRen ∘Ren σ ≡ σ
idRenL ! = refl
idRenL (σ ⊕ v) =
  W₂Ren idRen ∘Ren (σ ⊕ v)
    ≡⟨ ap (_⊕ v) (WRenLem₀ idRen σ v) ⟩
  (idRen ∘Ren σ) ⊕ v
    ≡⟨ ap (_⊕ v) (idRenL σ) ⟩
  σ ⊕ v
    ∎

idRenR : {n m : ℕ} (σ : Ren n m) → σ ∘Ren idRen ≡ σ
idRenR σ =
  mapVec (derive idRen) σ
    ≡⟨ (λ i → mapVec (λ v → deriveIdRen v i) σ) ⟩
  mapVec (λ v → v) σ
    ≡⟨ mapId σ ⟩
  σ
    ∎

WRenLem₄ : {n m : ℕ} (σ : Ren n m) →
  σ ∘Ren πRen ≡ W₁Ren σ
WRenLem₄ σ =
  σ ∘Ren πRen
    ≡⟨ WRenLem₁ σ idRen ⁻¹ ⟩
  W₁Ren (σ ∘Ren idRen)
    ≡⟨ ap W₁Ren (idRenR σ) ⟩
  W₁Ren σ
    ∎

WRenLem₅ : {n m : ℕ} (σ : Ren n m) (v : Fin n) →
  πRen ∘Ren (σ ⊕ v) ≡ σ
WRenLem₅ σ v =
  πRen ∘Ren (σ ⊕ v)
    ≡⟨ WRenLem₀ idRen σ v ⟩
  idRen ∘Ren σ
    ≡⟨ idRenL σ ⟩
  σ
    ∎

derive² : {n m k : ℕ} (σ : Ren m k) (τ : Ren n m) (v : Fin k) →
  derive τ (derive σ v) ≡ derive (σ ∘Ren τ) v
derive² σ τ 𝑍 = refl
derive² σ τ (𝑆 v) = derive² (πVec σ) τ v
