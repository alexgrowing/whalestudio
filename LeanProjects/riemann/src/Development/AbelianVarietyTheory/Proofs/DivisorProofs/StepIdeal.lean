import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero

set_option autoImplicit false

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.LieHt

namespace GlobalTheory.LieRead

variable {D : D7} (O : Setup D) {K : Type} [Field K] [NumberField K] (F : SemiFib K)

open Classical in

def stepVec (τ : D.host.E →+* ℂ) (j : ℕ) : Fin F.P₀.g → K := fun p =>
  if ∃ x : Letter O.S.Dw, x.1 = τ ∧ (x.2 : ℕ) = j ∧ (letters O.S.Dw)[(p : ℕ)]? = some x then 1 else 0

def stepCoef (τ : D.host.E →+* ℂ) (j : ℕ) : (Fin F.P₀.g → K) →ₗ[K] K :=
  ∑ p, stepVec O F τ j p • (LinearMap.proj p : (Fin F.P₀.g → K) →ₗ[K] K)

def stepIdeal (τ : D.host.E →+* ℂ) (i : ℕ) : Submodule (𝓞 K) K :=
  (stepLat O F τ (i + 1)).map ((stepCoef O F τ i).restrictScalars (𝓞 K))

def stepGrSq (h : HermFam K (Fin F.P₀.g → K)) (τ : D.host.E →+* ℂ) (i : ℕ) (σ : K →+* ℂ) : ℝ :=
  (h.gram σ fun j : Fin (i + 1) => stepVec O F τ j).det.re / (h.gram σ fun j : Fin i => stepVec O F τ j).det.re

open Classical in

def stepGrDeg (h : HermFam K (Fin F.P₀.g → K)) (τ : D.host.E →+* ℂ) (i : ℕ) : ℝ :=
  if ha : ∃ a ∈ stepIdeal O F τ i, a ≠ 0 then
    (Real.log ((Submodule.span (𝓞 K) {ha.choose}).toAddSubgroup.relIndex (stepIdeal O F τ i).toAddSubgroup : ℝ) -
      ∑ σ : K →+* ℂ, Real.log ‖σ ha.choose‖ - (1 / 2) * ∑ σ : K →+* ℂ, Real.log (stepGrSq O F h τ i σ)) /
      Module.finrank ℚ K
  else 0

end GlobalTheory.LieRead

end
