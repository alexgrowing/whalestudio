import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

def IsTateMeas {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (t : ℝ) (χ : kˣ →* ℂˣ) (e : ℂ) : Prop :=
  ∃ (c : kˣ) (a : ℕ) (R : Finset kˣ), HasConductor ψ c ∧ HasExponent χ a ∧ IsShellReps c a R ∧
    e = ((t * nabs k c : ℝ) : ℂ) * ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (r : k) : ℂ)

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

variable (A) in

abbrev EpsMeasFamily : Type 1 :=
  ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v), AddChar (v.adicCompletion L) Circle → ℝ → WD h → ℂˣ

structure IsDeligneMeas (ε : EpsMeasFamily A) : Prop where

  add : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion L) Circle), Continuous ψ → ψ ≠ 1 → ∀ t : ℝ, 0 < t →
    ∀ x y : WD h, ε L v h ψ t (x.lpSum y) = ε L v h ψ t x * ε L v h ψ t y

  scale : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion L) Circle), Continuous ψ → ψ ≠ 1 → ∀ t : ℝ, 0 < t →
    ∀ a : ℝ, 0 < a → ∀ x : WD h, (ε L v h ψ (a * t) x : ℂ) = (a : ℂ) ^ x.lpDim * ε L v h ψ t x

  ind : ∀ (K L : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'),
    IsLocalExt L h →
    ∀ (ψ : AddChar (v.adicCompletion K) Circle) (ψ' : AddChar (v'.adicCompletion L) Circle),
      Continuous ψ → ψ ≠ 1 → Continuous ψ' →
      (∀ z : L, ψ' (algebraMap L _ z) = ψ (algebraMap K _ (Algebra.trace K L z))) →
      ∀ t t' : ℝ, 0 < t → 0 < t' →
      ∀ (x₁ x₂ : WD h') (y₁ y₂ : WD h), Induces x₁ y₁ → Induces x₂ y₂ → x₁.lpDim = x₂.lpDim →
        ε K v h ψ t y₁ * ε L v' h' ψ' t' x₂ = ε K v h ψ t y₂ * ε L v' h' ψ' t' x₁

  char : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion L) Circle), Continuous ψ → ψ ≠ 1 → ∀ t : ℝ, 0 < t →
    ∀ (a : Weil h →* (v.adicCompletion L)ˣ) (ha : IsLocalArtin h a) (χ : (v.adicCompletion L)ˣ →* ℂˣ)
      (hχ : IsSmoothChar χ), IsTateMeas ψ t χ (ε L v h ψ t (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)))

end GlobalTheory.LocLanglands

end
