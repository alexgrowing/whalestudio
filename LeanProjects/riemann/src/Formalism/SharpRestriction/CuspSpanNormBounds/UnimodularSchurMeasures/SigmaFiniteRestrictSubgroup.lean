import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x1

variable {k r : ℕ}

theorem sigmaFinite_restrict_subgroup {U : Set (Mat k r)} (hU : IsClosedSubgroup U) (μ : Measure (Mt k r)) [SigmaFinite μ] :
    SigmaFinite (pull hU μ) := by
  refine (Measure.FiniteSpanningSetsIn.sigmaFinite (C := Set.univ)
    ⟨fun n => (inc : Gp U hU → Mt k r) ⁻¹' spanningSets μ n, fun _ => trivial, fun n => ?_, ?_⟩)
  · rw [pull, inc_memb.comap_apply]
    exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top μ n)
  · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]

theorem left_haar_eq_smul_biinvariant {U : Set (Mat k r)} (hU : IsClosedSubgroup U) {ν μ : Measure (Mt k r)}
    (hν : Formalism.FourierDecayAlt.B.IsHaarOn U ν) (hμ : Formalism.MainNotions.S.IsHaarOn U μ) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = c • ν := by
  obtain ⟨hσ, h0, hc, hl⟩ := hμ
  have hc' : μ Uᶜ = 0 := hc
  have : SigmaFinite ν := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hν
  have i1 : SigmaFinite (pull hU μ) := sigmaFinite_restrict_subgroup hU μ
  have i2 : SigmaFinite (pull hU ν) := sigmaFinite_restrict_subgroup hU ν
  have i3 : (pull hU μ).IsMulLeftInvariant := pull_left μ hl
  have i4 : (pull hU ν).IsMulLeftInvariant := pull_left ν hν.left
  have i5 : IsFiniteMeasureOnCompacts (pull hU ν) := pull_fin ν hν.finite_compact
  have hν0 : pull hU ν ≠ 0 := by
    intro h
    apply hν.ne_zero
    rw [← map_pull (hU := hU) ν hν.conc, h, Measure.map_zero]
  have hμ0 : pull hU μ ≠ 0 := by
    intro h
    apply h0
    rw [← map_pull (hU := hU) μ hc', h, Measure.map_zero]
  obtain ⟨K, hK, hK0⟩ := exists_pos (pull hU ν) hν0
  have hKt : pull hU ν K ≠ ∞ := hK.measure_lt_top.ne
  have key := measure_eq_div_smul (pull hU μ) (pull hU ν) hK0 hKt
  set c : ℝ≥0∞ := pull hU μ K / pull hU ν K with hcdef
  have hc0 : c ≠ 0 := by
    intro h
    apply hμ0
    rw [key, h, zero_smul]
  have hc1 : c ≠ ∞ := by
    intro h
    obtain ⟨n, hn⟩ := exists_pos_measure_of_cover (iUnion_spanningSets (pull hU μ)) hμ0
    have hfin := measure_spanningSets_lt_top (pull hU μ) n
    have e0 : ∀ s : Set (Gp U hU), pull hU μ s = ∞ * pull hU ν s := by
      intro s
      have := congrArg (fun m : Measure (Gp U hU) => m s) key
      simpa only [Measure.smul_apply, smul_eq_mul, h] using this
    have e := e0 (spanningSets (pull hU μ) n)
    by_cases hz : pull hU ν (spanningSets (pull hU μ) n) = 0
    · rw [e, hz, mul_zero] at hn
      exact lt_irrefl _ hn
    · rw [e, ENNReal.top_mul hz] at hfin
      exact lt_irrefl _ hfin
  refine ⟨c, hc0, hc1, ?_⟩
  calc μ = (pull hU μ).map inc := (map_pull μ hc').symm
    _ = (c • pull hU ν).map inc := by rw [← key]
    _ = c • ν := by rw [Measure.map_smul, map_pull ν hν.conc]

end Formalism.MainNotions.LeviCoordinates

end
