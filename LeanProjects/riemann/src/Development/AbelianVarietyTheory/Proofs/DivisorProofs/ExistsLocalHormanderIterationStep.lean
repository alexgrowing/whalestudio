import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HormanderEstimateOnBallConstLeviBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqNormSmoothSectionSubGluedLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEnergyGluedSectionLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSSecGlueSectionByPartitionOfHoloStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem hormander_step : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (t : ℝ), 0 < t → CurvGe C la t → ∀ F0 : ι → Y → ℂ, A.IsSSec (A.kap + la) F0 → ∃ F1 : ι → Y → ℂ, A.IsSSec (A.kap + la) F1 ∧ n0 A la (F0 - F1) ≤ ENNReal.ofReal (K / t) * n1 C la F0 ∧ n1 C la F1 ≤ ENNReal.ofReal (K / t) * n1 C la F0 := by
  intro n Y _ _ _ _ _ ι La _ A C
  obtain ⟨K', hK'0, hK'⟩ := GlobalTheory.T.dbar_energy_glued_section_le n Y ι La A C
  refine ⟨max (C.m : ℝ) K', le_max_of_le_right hK'0, ?_⟩
  intro la t ht hcurv F0 hF0
  have hball : ∀ a : Fin C.m, ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball (C.c a) (C.r a)) ∧
      ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - F v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) ≤
      ENNReal.ofReal t⁻¹ * ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
        ((∑ j, ‖wdb n j (F0 (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
    intro a
    have hsub : ball (C.c a) (C.r a) ⊆ (A.chart (C.idx a)).target :=
      ball_subset_closedBall.trans (C.sub a)
    refine GlobalTheory.T.hormander_estimate_on_ball_const_levi_bound n (C.c a) (C.r a) t (fun w => A.ph la (C.idx a) ((A.chart (C.idx a)).symm w))
      (F0 (C.idx a) ∘ (A.chart (C.idx a)).symm) ht ((A.smooth_ph la (C.idx a)).mono hsub)
      ((hF0.1 (C.idx a)).mono hsub) ?_
    intro v hv ξ
    have h := hcurv a v hv ξ
    unfold WeightedAtlas.leviAt at h
    rwa [(A.chart (C.idx a)).right_inv (hsub hv)] at h
  choose u hu hE using hball
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hE a)
  rw [← Finset.mul_sum] at hsum
  have hK : ENNReal.ofReal (max (C.m : ℝ) K' / t) =
      ENNReal.ofReal (max (C.m : ℝ) K') * ENNReal.ofReal t⁻¹ := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (le_max_of_le_right hK'0)]
  refine ⟨glue C la u, GlobalTheory.T.isSSec_glueSectionByPartition_of_holo n Y ι La A C la u hu, ?_, ?_⟩
  · have hm : (C.m : ℝ≥0∞) ≤ ENNReal.ofReal (max (C.m : ℝ) K') := by
      rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    calc n0 A la (F0 - glue C la u) ≤ _ := GlobalTheory.T.n0_sub_glue_le_card_mul_sum_lintegral n Y ι La A C la F0 u hF0 hu
      _ ≤ (C.m : ℝ≥0∞) * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by gcongr; exact hsum
      _ ≤ ENNReal.ofReal (max (C.m : ℝ) K') * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by gcongr
      _ = _ := by rw [hK, mul_assoc]
  · calc n1 C la (glue C la u) ≤ _ := hK' la F0 u hF0 hu
      _ ≤ ENNReal.ofReal K' * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by gcongr; exact hsum
      _ ≤ ENNReal.ofReal (max (C.m : ℝ) K') * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by
        gcongr; exact le_max_right _ _
      _ = _ := by rw [hK, mul_assoc]

end GlobalTheory
