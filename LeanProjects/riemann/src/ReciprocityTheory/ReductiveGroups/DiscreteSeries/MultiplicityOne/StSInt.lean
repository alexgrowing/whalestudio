import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeConvA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stSInt (h : UnitaryGroupStructuralFacts) : StSInt := by
  intro k r Wp _ _ _ D hD b hb
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGL, -, -, -, hCG, -⟩, -⟩ := id h
  have sW := bc_isHaarOn_sigmaFinite D.haarW
  have sN := bc_isHaarOn_sigmaFinite D.haarN
  have hfin := bc_lintegral_S_pow_AB h D (by rw [hD.μW_eq])
  have hAB1 : 1 ≤ AB k r := by
    rw [AB]; have := Nat.cast_nonneg (α := ℝ) k; have := Nat.cast_nonneg (α := ℝ) r; nlinarith
  have hmeas : Measurable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) :=
    ((bc_gN_cont_mt.comp (bc_continuous_mulM.comp continuous_swap)).measurable).pow_const _
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => Real.rpow_nonneg (bc_gN_nonneg _) _)]
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hfin
  have aeS : ∀ᵐ p1 ∂(D.μW.prod D.μN), (Matrix.of p1.1 : Mat k r) ∈ UWset k r D.z ∧
      (Matrix.of p1.2 : Mat k r) ∈ Nset k r :=
    bc_ae_prod_and (bc_isHaarOn_ae_mem D.haarW) (bc_isHaarOn_ae_mem D.haarN)
  filter_upwards [aeS] with p hp
  have hG : (Matrix.of p.2 : Mat k r) * Matrix.of p.1 ∈ GV k r := (hCG k r).mul_mem _ hp.2.1 _ hp.1.1
  change ENNReal.ofReal (gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) ≤
    ENNReal.ofReal (gN (Matrix.of p.2 * Matrix.of p.1) ^ (-AB k r))
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (hGL k r _ hG) (by linarith))

end ReciprocityTheory.ChartRestriction.DS.Mult1
