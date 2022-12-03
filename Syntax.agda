{-# OPTIONS --cubical --rewriting #-}

module Syntax where

open import Binary
open import Ren

open import Cubical.Data.Nat

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

{-# BUILTIN REWRITE _≡_ #-}

---------------------------------------------------------------------------
-- Untyped Syntax

data Tm : ℕ → ℕ → Type where
  Pos : {n m : ℕ} → Fin n → Tm n m
  V : {n m : ℕ} → Fin m → Tm n m
  App : {n m : ℕ} → Tm n m → Tm n m → Tm n m

data Ty : ℕ → ℕ → Type where
  𝒰 : {n m : ℕ} → Ty n m
  El : {n m : ℕ} → Tm n m → Ty n m
  Π : {n m : ℕ} → Ty n m → Ty n (suc m) → Ty n m

Tms : ℕ → ℕ → ℕ → Type
Tms n m k = Vec (Tm n m) k

infixl 20 _[_]TmRen _[_]TyRen

_[_]TmRen : {n m k : ℕ} → Tm k m → Ren n m → Tm k n
Pos n [ σ ]TmRen = Pos n
V n [ σ ]TmRen = V (derive σ n)
App E F [ σ ]TmRen = App (E [ σ ]TmRen) (F [ σ ]TmRen)

_[_]TyRen : {n m k : ℕ} → Ty k m → Ren n m → Ty k n
𝒰 [ σ ]TyRen = 𝒰
El E [ σ ]TyRen = El (E [ σ ]TmRen)
Π T S [ σ ]TyRen = Π (T [ σ ]TyRen) (S [ W₂Ren σ ]TyRen)

WTm : {n m : ℕ} → Tm n m → Tm n (suc m)
WTm E = E [ πRen ]TmRen

WTy : {n m : ℕ} → Ty n m → Ty n (suc m)
WTy T = T [ πRen ]TyRen

W₁Tms : {n m k : ℕ} → Tms n m k → Tms n (suc m) k
W₁Tms σ = mapVec WTm σ

W₂Tms : {n m k : ℕ} → Tms n m k → Tms n (suc m) (suc k)
W₂Tms σ = W₁Tms σ ⊕ V 𝑍

infixl 20 _[_]Tm _[_]Ty

_[_]Tm : {n m k : ℕ} → Tm k m → Tms k n m → Tm k n
Pos n [ σ ]Tm = Pos n
V n [ σ ]Tm = derive σ n
App E F [ σ ]Tm = App (E [ σ ]Tm) (F [ σ ]Tm)

_[_]Ty : {n m k : ℕ} → Ty k m → Tms k n m → Ty k n
𝒰 [ σ ]Ty = 𝒰
El E [ σ ]Ty = El (E [ σ ]Tm)
Π T S [ σ ]Ty = Π (T [ σ ]Ty) (S [ W₂Tms σ ]Ty)

idTms : {n m : ℕ} → Tms m n n
idTms = mapVec V idRen

WTmP : {k n : ℕ} → Tm k n → Tm (suc k) n
WTmP (Pos n) = Pos (𝑆 n)
WTmP (V n) = V n
WTmP (App E F) = App (WTmP E) (WTmP F)

WTyP : {k n : ℕ} → Ty k n → Ty (suc k) n
WTyP 𝒰 = 𝒰
WTyP (El E) = El (WTmP E)
WTyP (Π T S) = Π (WTyP T) (WTyP S)

infixl 10 _⊹_
data Seq (A : ℕ → Type ℓ) : ℕ → Type ℓ where
  ∅ : Seq A 0
  _⊹_ : {n : ℕ} → Seq A n → A n → Seq A (suc n)

Ctx : ℕ → ℕ → Type
Ctx k n = Seq (Ty k) n

ExprCtx : ℕ → ℕ → Type
ExprCtx k n = Seq (Tm k) n

PCtx : ℕ → Type
PCtx n = Seq (λ k → Ty k 0) n

mapSeq : {A : ℕ → Type ℓ₁} {B : ℕ → Type ℓ₂} (f : {n : ℕ} → A n → B n)
  {n : ℕ} → Seq A n → Seq B n
mapSeq f ∅ = ∅
mapSeq f (σ ⊹ t) = mapSeq f σ ⊹ f t

---------------------------------------------------------------------------
-- Construction of Untyped SST Expressions

fold : {k n : ℕ} → Ctx k n → Ty k n → Ty k 0
fold ∅ S = S
fold (G ⊹ T) S = fold G (Π T S)

makeFin : {n k : ℕ} → k < n → Fin n
makeFin n<Sn = 𝑍
makeFin (n<Sm p) = 𝑆 (makeFin p)

make-neu : {k n m l : ℕ} → l < k → Subset n m → Tm k n
make-neu p done = Pos (makeFin p)
make-neu p (yes d) = App (WTm (make-neu p d)) (V 𝑍)
make-neu p (no d) = WTm (make-neu p d)

make-neus : {k n : ℕ} (l : DepList n) → DimBounded k l → ExprCtx k n
make-neus [] ⋆ = ∅
make-neus (l ∷⟨ n ⊚ X ⟩) (n<k , p) = make-neus l p ⊹ make-neu n<k X

Δ-Type : (n : ℕ) → Ty n 0
Δ-Type n = fold (mapSeq El (make-neus (∂Δ n) (∂-dim n))) 𝒰

Δ-Pos : (n : ℕ) → PCtx n
Δ-Pos zero = ∅
Δ-Pos (suc n) = Δ-Pos n ⊹ Δ-Type n

---------------------------------------------------------------------------
-- Variables and Renamings

data PVar : {k : ℕ} (P : PCtx k) (m : Fin k) (T : Ty k 0) → Type where
  𝑧𝑣 : {k : ℕ} {P : PCtx k} {T : Ty k 0} →
    PVar (P ⊹ T) 𝑍 (WTyP T)
  𝑠𝑣 : {k : ℕ} {P : PCtx k} {T S : Ty k 0} {m : Fin k} →
    PVar P m S → PVar (P ⊹ T) (𝑆 m) (WTyP S)

data Var : {k n : ℕ} (G : Ctx k n) (m : Fin n) (T : Ty k n) → Type where
  𝑧𝑣 : {k n : ℕ} {G : Ctx k n} {T : Ty k n} →
    Var (G ⊹ T) 𝑍 (WTy T)
  𝑠𝑣 : {k n : ℕ} {G : Ctx k n} {T S : Ty k n} {m : Fin n} →
    Var G m S → Var (G ⊹ T) (𝑆 m) (WTy S)

---------------------------------------------------------------------------
-- Typing Laws

data V-PCtx : {k : ℕ} → PCtx k → Type
data V-Ctx : {k n : ℕ} → PCtx k → Ctx k n → Type
data V-Tms : {k n m : ℕ} → PCtx k → Ctx k n → Tms k n m → Ctx k m → Type
data V-Ty : {k n : ℕ} → PCtx k → Ctx k n → Ty k n → Type
data V-Tm : {k n : ℕ} → PCtx k → Ctx k n → Tm k n → Ty k n → Type

data V-PCtx where
  ∅ : V-PCtx ∅
  _⊹_ : {k : ℕ} {P : PCtx k} {T : Ty k 0} →
    V-PCtx P → V-Ty P ∅ T → V-PCtx (P ⊹ T)

data V-Ctx where
  ∅ : {k : ℕ} {P : PCtx k} → V-Ctx P ∅
  _⊹_ : {n m : ℕ} {P : PCtx n} {G : Ctx n m} {T : Ty n m} →
    V-Ctx P G → V-Ty P G T → V-Ctx P (G ⊹ T)

data V-Tms where
  ! : {k n : ℕ} {P : PCtx k} {G : Ctx k n} →
    V-Tms P G ! ∅
  _⊕_ : {k n m : ℕ} {P : PCtx k} {G : Ctx k n}
    {D : Ctx k m} {ES : Tms k n m} {E : Tm k n} {T : Ty k m}
    (σ : V-Tms P G ES D) (t : V-Tm P G E (T [ ES ]Ty)) →
    V-Tms P G (ES ⊕ E) (D ⊹ T)

data V-Ty where
  R-Ty : {k n : ℕ} {P : PCtx k} {G : Ctx k n} → V-Ty P G 𝒰
  R-Π : {k n : ℕ} {P : PCtx k} {G : Ctx k n} {T : Ty k n}
    {S : Ty k (suc n)} → V-Ty P G T → V-Ty P (G ⊹ T) S →
    V-Ty P G (Π T S)
  R-El : {k n : ℕ} {P : PCtx k} {G : Ctx k n} {E : Tm k n} →
    V-Tm P G E 𝒰 → V-Ty P G (El E)

data V-Tm where
  R-Var : {k n : ℕ} {P : PCtx k} {G : Ctx k n} {T : Ty k n}
    {m : Fin n} → Var G m T → V-Tm P G (V m) T
  R-Pos : {k n : ℕ} {P : PCtx k} {G : Ctx k n} {T : Ty k 0}
    {m : Fin k} → PVar P m T  → V-Tm P G (Pos m) (T [ ! ]TyRen)
  R-App : {k n : ℕ} {P : PCtx k} {G : Ctx k n}
    {E₁ E₂ : Tm k n} {T : Ty k n} {S : Ty k (suc n)} → V-Ty P G (Π T S) →
    (t : V-Tm P G E₁ (Π T S)) (s : V-Tm P G E₂ T) →
    V-Tm P G (App E₁ E₂) (S [ idTms ⊕ E₂ ]Ty)

---------------------------------------------------------------------------
-- Extras

[][]TmRen : {k n m l : ℕ} (E : Tm k l) (σ : Ren m l) (τ : Ren n m) →
  E [ σ ]TmRen [ τ ]TmRen ≡ E [ σ ∘Ren τ ]TmRen
[][]TmRen (Pos n) σ τ = refl
[][]TmRen (V n) σ τ = ap V (derive² σ τ n)
[][]TmRen (App E F) σ τ =
  cong₂ App ([][]TmRen E σ τ) ([][]TmRen F σ τ)

[][]TyRen : {k n m l : ℕ} (T : Ty k l) (σ : Ren m l) (τ : Ren n m) →
  T [ σ ]TyRen [ τ ]TyRen ≡ T [ σ ∘Ren τ ]TyRen
[][]TyRen 𝒰 σ τ = refl
[][]TyRen (El E) σ τ = ap El ([][]TmRen E σ τ)
[][]TyRen (Π T S) σ τ =
  cong₂ Π
    ([][]TyRen T σ τ)
    ([][]TyRen S (W₂Ren σ) (W₂Ren τ)
      ∙ ap (S [_]TyRen) (WRenLem₃ σ τ ⁻¹))

W[]TyRen₁ : {n m k : ℕ} (T : Ty k m) (σ : Ren n m) →
  T [ σ ]TyRen [ πRen ]TyRen ≡ T [ W₁Ren σ ]TyRen
W[]TyRen₁ T σ = [][]TyRen T σ πRen ∙ ap (T [_]TyRen) (WRenLem₄ σ)

W[]TyRen₂ : {n m k : ℕ} (T : Ty k m) (σ : Ren n m) (v : Fin n) →
  T [ πRen ]TyRen [ σ ⊕ v ]TyRen ≡ T [ σ ]TyRen
W[]TyRen₂ T σ v = [][]TyRen T πRen (σ ⊕ v) ∙ ap (T [_]TyRen) (WRenLem₅ σ v)

{-# REWRITE W[]TyRen₁ W[]TyRen₂ #-}

data V-Ren : {k n m : ℕ} → (G : Ctx k n) (VS : Ren n m) (D : Ctx k m) →
              Type where
  ! : {k n : ℕ} {G : Ctx k n} → V-Ren G ! ∅
  _⊕_ : {k n m : ℕ} {G : Ctx k n} {VS : Ren n m} {v : Fin n}
    {D : Ctx k m} {T : Ty k m}  →
    V-Ren G VS D → Var G v (T [ VS ]TyRen) → V-Ren G (VS ⊕ v) (D ⊹ T)

W₁V-Ren : {k n m : ℕ} {G : Ctx k n} {D : Ctx k m} {VS : Ren n m}
  {T : Ty k n} → V-Ren G VS D → V-Ren (G ⊹ T) (W₁Ren VS) D
W₁V-Ren ! = !
W₁V-Ren (σ ⊕ v) = W₁V-Ren σ ⊕ 𝑠𝑣 v

W₂V-Ren : {k n m : ℕ} {G : Ctx k n} {D : Ctx k m}
  {VS : Ren n m} {T : Ty k m} →
  V-Ren G VS D → V-Ren (G ⊹ (T [ VS ]TyRen)) (W₂Ren VS) (D ⊹ T)
W₂V-Ren σ = W₁V-Ren σ ⊕ 𝑧𝑣

-- can be used to define weakenings of type derivations...
