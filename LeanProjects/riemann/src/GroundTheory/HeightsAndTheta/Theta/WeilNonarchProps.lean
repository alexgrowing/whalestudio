import Mathlib
import GroundTheory.HeightsAndTheta.Theta.WeilNonarch
import GroundTheory.LocalFields.LocalZeta

noncomputable section

namespace GroundTheory.Heights₂.Theta

open GroundTheory.LocalField ValuativeRel MeasureTheory Measure Topology Filter Matrix
open scoped WithZero NNReal ENNReal Pointwise ComplexConjugate

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [MeasurableSpace F] [BorelSpace F] {ψ : AddChar F Circle}

section ChangeOfVariables

def linearEquivHomeomorph (L : (ι → F) ≃ₗ[F] (ι → F)) : (ι → F) ≃ₜ (ι → F) where
  toEquiv := L.toEquiv
  continuous_toFun := L.toLinearMap.continuous_on_pi
  continuous_invFun := L.symm.toLinearMap.continuous_on_pi

theorem distribHaarChar_linearEquiv (L : (ι → F) ≃ₗ[F] (ι → F)) :
    distribHaarChar (ι → F) L = modulus (LinearEquiv.det L : F) := by
  rw [GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq, distribHaarChar_eq_modulus]

theorem map_linearEquiv_selfDualPi (L : (ι → F) ≃ₗ[F] (ι → F)) :
    Measure.map L (selfDualPi ι ψ) =
      ((modulus (LinearEquiv.det L : F))⁻¹ : ℝ≥0) • selfDualPi ι ψ := by
  have hL : Measurable (L : (ι → F) → (ι → F)) :=
    (linearEquivHomeomorph L).continuous.measurable
  ext s hs
  rw [Measure.map_apply hL hs, Measure.smul_apply]
  have hpre : (L : (ι → F) → (ι → F)) ⁻¹' s = L⁻¹ • s := by
    ext x
    simp [Set.mem_smul_set_iff_inv_smul_mem, LinearEquiv.smul_def]
  rw [hpre, ← distribHaarChar_mul, map_inv, distribHaarChar_linearEquiv, ENNReal.smul_def,
    smul_eq_mul]

theorem integral_comp_linearEquiv (L : (ι → F) ≃ₗ[F] (ι → F)) (g : (ι → F) → ℂ) :
    ∫ x, g (L x) ∂selfDualPi ι ψ =
      (((modulus (LinearEquiv.det L : F))⁻¹ : ℝ≥0) : ℝ) * ∫ x, g x ∂selfDualPi ι ψ := by
  have h := integral_map_equiv (μ := selfDualPi ι ψ) (linearEquivHomeomorph L).toMeasurableEquiv g
  have he : ((linearEquivHomeomorph L).toMeasurableEquiv : (ι → F) → (ι → F)) = L := rfl
  rw [he, map_linearEquiv_selfDualPi, integral_smul_nnreal_measure] at h
  rw [← h, NNReal.smul_def, Complex.real_smul]

theorem integral_comp_mulVec {P : Matrix ι ι F} (hP : P.det ≠ 0) (g : (ι → F) → ℂ) :
    ∫ x, g (P *ᵥ x) ∂selfDualPi ι ψ =
      (((modulus P.det)⁻¹ : ℝ≥0) : ℝ) * ∫ x, g x ∂selfDualPi ι ψ := by
  set G := Matrix.GeneralLinearGroup.mkOfDetNeZero P hP
  have h1 : ∀ x, GroundTheory.Automorphic.Measures.glEquiv G x = P *ᵥ x := fun x =>
    GroundTheory.Automorphic.Measures.glEquiv_apply G x
  have h2 : (LinearEquiv.det (GroundTheory.Automorphic.Measures.glEquiv G) : F) = P.det := by
    rw [GroundTheory.Automorphic.Measures.det_glEquiv]
    rfl
  have := integral_comp_linearEquiv (ψ := ψ) (GroundTheory.Automorphic.Measures.glEquiv G) g
  simp_rw [h1, h2] at this
  exact this

end ChangeOfVariables

section Subgroups

def gaussSet (ψ : AddChar F Circle) (A : Matrix ι ι F) (Λ : Set (ι → F)) : ℂ :=
  ∫ x in Λ, (ψ (quadForm A x) : ℂ) ∂selfDualPi ι ψ

variable (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ

include hψ1

end Subgroups

section Isometry

variable (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1

end Isometry

section Neg

variable (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1

end Neg

section OrthogonalSum

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

variable (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1

end OrthogonalSum

end GroundTheory.Heights₂.Theta
