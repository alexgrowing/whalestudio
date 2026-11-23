import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.GfEqOfZhat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFlWitt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FibreOrbits.FibreOrbitOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedFrameProperty
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Gram

theorem fibreOrbit_all : C2.FibreOrbit :=
  PI.UnitaryGroupMassFormula.FibOrbAsmW.fibreOrbit_of (fun k r _ _ x y hx hy hg => PI.UnitaryGroupMassFormula.DLm.Lifts.wittHpk k r x y hx hy hg)
    Formalism.FourierDecayAlt.P.fixed_frame_property Formalism.FourierDecayAlt.P.gram_block_form Formalism.FourierDecayAlt.P.gram_independent_signature'

theorem parabolic_levi_unipotent_decomp {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {s : B.Mat k r}
    (hs : s ∈ C2.CurvatureSupportSet k r z) : ∃ h ∈ UWset k r z, ∃ m ∈ C2.N0set k r z, s = h * m := by
  obtain ⟨⟨h, hh, m, hm, rfl⟩, hu⟩ := hs
  have hF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz
  have h1N : (1 : B.Mat k r) ∈ Nset k r := ((PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz).one_mem).1
  have hS_h : h ∈ Sset k r z := ⟨h, hh, 1, h1N, (mul_one h).symm⟩
  have hS_m : m ∈ Sset k r z := ⟨1, one_mem_UW z, m, hm, (one_mul m).symm⟩
  have e := (hF.1 h hS_h).2.2 m hS_m
  rw [hF.2 h hh, Matrix.one_mul, hu] at e
  exact ⟨h, hh, m, ⟨hm, e.symm⟩, rfl⟩

theorem gram_schmidt_witt : GsWitt := by
  intro k r z z' hk hr hz hz' g₁ hg₁ g₂ hg₂ hG hZ
  obtain ⟨s, hs, s', hs', e⟩ := fibreOrbit_all k r z z' ⟨hk, hz, hz'⟩ g₁ hg₁ g₂ hg₂ hG hZ
  obtain ⟨h, hh, m, hm, rfl⟩ := parabolic_levi_unipotent_decomp hz hs
  obtain ⟨h', hh', m', hm', rfl⟩ := parabolic_levi_unipotent_decomp hz' hs'
  have Gz := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz
  have Gz' := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z' hz'
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have hhu := Wz.unit h hh
  have hhu' := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z').unit h' hh'
  have hx : h * m⁻¹ * h⁻¹ ∈ C2.N0set k r z := unipotent_normal_unitary hz hh (Gz.inv_mem m hm)
  refine ⟨h⁻¹, Wz.inv_mem h hh, (h * m⁻¹ * h⁻¹)⁻¹, Gz.inv_mem _ hx, h' * m' * h'⁻¹, unipotent_normal_unitary hz' hh' hm', h', hh',
    ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv _ (Gz.unit _ hx), e, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hhu, Matrix.nonsing_inv_mul h' hhu',
    Matrix.mul_one]

end PI.UnitaryGroupMassFormula.DLm.Gram
