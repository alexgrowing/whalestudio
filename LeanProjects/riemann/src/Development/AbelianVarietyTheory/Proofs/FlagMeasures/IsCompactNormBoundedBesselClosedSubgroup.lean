import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

open scoped Matrix.Norms.L2Operator in

theorem isCompact_closed_inter_opn_le {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ)) (hS : IsClosed S)
    (R : ℝ) : IsCompact {g | g ∈ S ∧ opn g ≤ R} := by

  let e := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv
  have hK : IsCompact (e ⁻¹' Metric.closedBall 0 R) :=
    e.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  have hset : {g | g ∈ S ∧ opn g ≤ R} = S ∩ e ⁻¹' Metric.closedBall 0 R := by
    ext g
    simp [opn, e, mem_closedBall_zero_iff]
  rw [hset]
  exact hK.inter_left hS

theorem isCompact_normBounded : ∀ (k r : ℕ) (S : Set (Mat k r)), IsClosedSub k r S →
    ∀ R : ℝ, IsCompact {g | g ∈ S ∧ opn g ≤ R} := by
  intro k r S hS R
  exact isCompact_closed_inter_opn_le S hS.2.1 R

end GlobalTheory.SgInf
