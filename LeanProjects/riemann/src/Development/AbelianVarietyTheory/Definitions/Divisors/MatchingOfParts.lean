import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

namespace GlobalTheory.ThK

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def KDecay : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → Decay B G om om'

def KConst : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om' R Rf, IsMatched B G X om om' R Rf → OneConst B G X om om' R Rf

def KCoinv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om' R Rf, IsMatched B G X om om' R Rf → Coinv B G X om om' Rf

def KBeta : Prop :=
  ∃ e₁ e₂ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    StepBeta σ e₁ e₂ s

def KAlpha : Prop :=
  ∃ e₁ e₂ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    StepAlpha σ e₁ e₂ s

def KReal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∃ R, IsRealMaps B G om om' R

def KFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∃ Rf, IsFinMaps B G X om om' Rf

theorem agree_of_parts (h1 : KDecay) (h2 : KConst) (h3 : KCoinv) (h4 : KBeta) (h5 : KAlpha) : ThetaIntegralsAgree :=
  ⟨fun F E _ _ _ _ _ σ B a a' G X om om' h => ⟨h1 F E σ B a a' G X om om' h,
    fun R Rf m => ⟨h2 F E σ B a a' G X om om' R Rf m, h3 F E σ B a a' G X om om' R Rf m⟩⟩, h4, h5⟩

theorem matching_of_parts (h1 : KReal) (h2 : KFin) : LocalMatching := fun F E _ _ _ _ _ σ B a a' G X om om' h =>
  let ⟨R, r⟩ := h1 F E σ B a a' G X om om' h
  let ⟨Rf, f⟩ := h2 F E σ B a a' G X om om' h
  ⟨R, Rf, h, r, f⟩

end GlobalTheory.ThK
