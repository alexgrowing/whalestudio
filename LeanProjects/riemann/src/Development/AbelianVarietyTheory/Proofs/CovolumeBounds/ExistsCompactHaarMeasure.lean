import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MaximalCompactSubgroupPropertiesStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi

theorem exists_isKMeas : ∀ k r : ℕ, ∃ μK : Measure (Mt k r), IsKMeas k r μK := by
  intro k r
  obtain ⟨hcl, hco, -⟩ := GlobalTheory.T.maximal_compact_subgroup_properties k r
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.compact_group_haar_exists k r (Kset k r) hcl hco
  have hfin : μ Set.univ < ∞ := by
    have h1 : μ Set.univ ≤ μ (Kset k r) + μ (Kset k r)ᶜ := measure_univ_le_add_compl _
    have h2 : μ (Kset k r) < ∞ := hμ.finite_compact _ hco
    rw [hμ.conc, add_zero] at h1
    exact h1.trans_lt h2
  have hne : μ Set.univ ≠ 0 := by
    intro h
    exact hμ.ne_zero (Measure.measure_univ_eq_zero.1 h)
  have hone : ((μ Set.univ)⁻¹ • μ) Set.univ = 1 := by
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hne hfin.ne]
  refine ⟨(μ Set.univ)⁻¹ • μ, ⟨?_, ?_, ?_, ?_, ?_⟩, hone⟩
  · rw [Measure.smul_apply, hμ.conc, smul_zero]
  · intro a ha
    rw [Measure.map_smul, hμ.left a ha]
  · intro a ha
    rw [Measure.map_smul, hμ.right a ha]
  · intro K _
    calc _ ≤ ((μ Set.univ)⁻¹ • μ) Set.univ := measure_mono (Set.subset_univ _)
      _ < ∞ := by rw [hone]; exact ENNReal.one_lt_top
  · intro h
    rw [h] at hone
    simp at hone

end GlobalTheory.HCXi
