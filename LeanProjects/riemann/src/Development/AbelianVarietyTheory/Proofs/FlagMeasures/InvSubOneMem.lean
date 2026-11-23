import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.GaugeSubLoc

variable {n : ℕ} {ε : Fin n → Bool}

theorem uMat_mul (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_one : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel, uMat_one]

theorem uMat_inv_mul (g : Formalism.REAL.UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel, uMat_one]

theorem inv_sub_one_mem (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A)
    (g : Formalism.REAL.UJ ε) (hg : uMat g - 1 ∈ A) : uMat g⁻¹ - 1 ∈ A := by

  have hmap : ∀ W : A, uMat g * (W : Matrix (Fin n) (Fin n) ℂ) ∈ A := by
    intro W
    have : uMat g * (W : Matrix (Fin n) (Fin n) ℂ) = (uMat g - 1) * W + W := by noncomm_ring
    rw [this]
    exact A.add_mem (hA _ hg _ W.2) W.2
  let T : A →ₗ[ℝ] A :=
    LinearMap.codRestrict A ((LinearMap.mulLeft ℝ (uMat g)).comp A.subtype) hmap
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro W hW
    have h0 : uMat g * (W : Matrix (Fin n) (Fin n) ℂ) = 0 := congrArg Subtype.val hW
    apply Subtype.ext
    calc (W : Matrix (Fin n) (Fin n) ℂ) = uMat g⁻¹ * (uMat g * W) := by
          rw [← Matrix.mul_assoc, uMat_inv_mul, Matrix.one_mul]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  obtain ⟨W, hW⟩ := (LinearMap.injective_iff_surjective (f := T)).mp hinj ⟨-(uMat g - 1), A.neg_mem hg⟩
  have hW' : uMat g * (W : Matrix (Fin n) (Fin n) ℂ) = -(uMat g - 1) := congrArg Subtype.val hW
  have hinv : uMat g⁻¹ = 1 + (W : Matrix (Fin n) (Fin n) ℂ) := by
    calc uMat g⁻¹ = uMat g⁻¹ * (uMat g * (1 + (W : Matrix (Fin n) (Fin n) ℂ))) := by
          rw [Matrix.mul_add, Matrix.mul_one, hW', show uMat g + -(uMat g - 1) = 1 by abel,
            Matrix.mul_one]
      _ = 1 + (W : Matrix (Fin n) (Fin n) ℂ) := by
          rw [← Matrix.mul_assoc, uMat_inv_mul, Matrix.one_mul]
  rw [hinv, add_sub_cancel_left]
  exact W.2

def algSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : Subgroup (Formalism.REAL.UJ ε) where
  carrier := {g | uMat g - 1 ∈ A}
  one_mem' := by simp [uMat_one]
  mul_mem' := by
    intro g h hg hh
    have : uMat (g * h) - 1 = (uMat g - 1) * (uMat h - 1) + (uMat g - 1) + (uMat h - 1) := by
      rw [uMat_mul]; noncomm_ring
    change uMat (g * h) - 1 ∈ A
    rw [this]
    exact A.add_mem (A.add_mem (hA _ hg _ hh) hg) hh
  inv_mem' := fun {g} hg => inv_sub_one_mem A hA g hg

theorem isClosed_algSub (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : IsClosed (algSub ε A hA : Set (Formalism.REAL.UJ ε)) := by
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => uMat g - 1) :=
    (Units.continuous_val.comp continuous_subtype_val).sub continuous_const
  exact A.closed_of_finiteDimensional.preimage hc

end GlobalTheory.GaugeSubLoc
