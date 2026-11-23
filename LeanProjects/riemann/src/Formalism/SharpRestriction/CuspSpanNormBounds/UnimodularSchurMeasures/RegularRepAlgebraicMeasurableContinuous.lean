import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ProjectionCountCuspOfTrivialIdempotent
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ArchimedeanRestrictionStronglyContinuous

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem packet_bound_of_volume_kernel_conditions (cε C₁ c₁ A A₂ : ℝ) (hcε : 0 < cε) (hcε2 : cε ≤ 1 / 2) (hC₁ : 1 ≤ C₁) (hc₁ : 0 < c₁)
    (hA : 1 ≤ A) (hA₂ : 0 ≤ A₂) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ n₁ : ℕ, ∀ Cb : ℝ, ∃ C₂ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (C cb : ℝ),
      n₁ ≤ n₀ → C₂ ≤ C → adm2 D → DiscreteSeriesDecayBound D → Conclusion2 D n₀ A Cb → KernelDiagonalVolumeModulusConditions n₀ A C cb c₁ A₂ cε C₁ →
      PointsLemma D n₀ A C c' cb := by
  obtain ⟨c', hc', n₁, h⟩ := third_part_of_final_estimates cε C₁ c₁ A A₂ hcε hcε2 hC₁ hc₁ hA hA₂
  refine ⟨c', hc', n₁, fun Cb => ?_⟩
  obtain ⟨C₂, h2⟩ := h Cb
  exact ⟨C₂, fun D n₀ C cb a b c d e f => h2 D n₀ C cb a b c d e ((kernel_conditions_iff_without_regular_rep n₀ A C cb c₁ A₂ cε C₁).2 f)⟩

theorem regular_rep_algebraic_measurable_continuous (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (hu : UnimodF X) :
    RepAlg X ∧ (∀ x y : X.L2, StronglyMeasurable fun g => ⟪x, X.R g y⟫_ℂ) ∧ RepInf X :=
  have hd := RegData_of_HypB X hX
  have ha := UnimodA_of_UnimodF X hu
  ⟨rightRegular_isometric_multiplicative X hd ha, regular_rep_coeff_measurable X hd ha, archimedean_restriction_strongly_continuous X hd ha⟩

end Formalism.MainNotions.LeviCoordinates

end
