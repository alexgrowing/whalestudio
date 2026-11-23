import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFgFib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundX
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnitaryWeylCompact
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Gram

theorem unipotent_normal_unitary {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {a u : B.Mat k r}
    (ha : a ∈ UWset k r z) (hu : u ∈ C2.N0set k r z) : a * u * a⁻¹ ∈ C2.N0set k r z := by
  have hN := (unitary_weyl_normal_holds k r z hz.1 a ha u hu.1).1
  have hF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz
  have h1N : (1 : B.Mat k r) ∈ Nset k r := ((PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz).one_mem).1
  have hS_a : a ∈ Sset k r z := ⟨a, ha, 1, h1N, (mul_one a).symm⟩
  have hS_u : u ∈ Sset k r z := ⟨1, one_mem_UW z, u, hu.1, (one_mul u).symm⟩
  have hS_c : a * u * a⁻¹ ∈ Sset k r z := ⟨1, one_mem_UW z, _, hN, (one_mul _).symm⟩
  have hua : IsUnit a.det := WeylGroupFacts.isUnit_of_uh ha.1
  have e : a * u * a⁻¹ * a = a * u := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hua, Matrix.mul_one]
  have h2 := (hF.1 _ hS_c).2.2 a hS_a
  have h3 := (hF.1 a hS_a).2.2 u hS_u
  refine ⟨hN, ?_⟩
  rw [e, h3, hF.2 a ha, hu.2] at h2
  simpa using h2.symm

end PI.UnitaryGroupMassFormula.DLm.Gram
