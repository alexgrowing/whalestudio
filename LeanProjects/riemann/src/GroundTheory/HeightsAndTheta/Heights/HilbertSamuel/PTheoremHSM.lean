import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionSup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem resolutionVolumeL2_le_sqrt_two_mul (d : HSMDatum D Ω κ) (n : ℕ) (f : MvPolynomial (Ix κ) ℤ) :
    resolutionVolumeL2 d n f ≤ Real.sqrt 2 * resolutionSectionL2Norm d n f := by
  unfold resolutionVolumeL2 resolutionSectionL2Norm
  rw [← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  have hb : 0 ≤ ∫ y, ptNorm d.m (Int.castRingHom ℂ) n f (conjPt (resPt d y)) ^ 2 ∂d.dV :=
    integral_nonneg fun y => sq_nonneg _
  linarith

theorem TheoremHSM.proof (h₁ : ReductionToProjective.Statement) (h₂ : HilbertSamuelProjective.Statement)
    (h₃ : ResolutionSupBound.Statement) : TheoremHSM.Statement := by
  intro D Ω _ _ κ _ I d hI
  refine ⟨?_, ?_⟩
  · have hA := (h₁ D Ω κ I d hI).2
    have hB := (h₂ D I hI).const_mul_left (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ)
    exact (hA.add hB).congr_left fun n => by ring
  · obtain ⟨C, hC⟩ := ResolutionSupBound.toInt h₃ D Ω κ d
    refine ⟨max C 0 * Real.sqrt 2, fun n hn f hf z hz => ?_⟩
    have hp : 0 ≤ (n : ℝ) ^ ((D : ℝ) / 2) := by positivity
    have hv : 0 ≤ resolutionVolumeL2 d n f := Real.sqrt_nonneg _
    calc ptNorm d.m (Int.castRingHom ℂ) n f z ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2 d n f :=
          hC n hn f hf z hz
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2 d n f :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hp) hv
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * (Real.sqrt 2 * resolutionSectionL2Norm d n f) :=
          mul_le_mul_of_nonneg_left (resolutionVolumeL2_le_sqrt_two_mul d n f)
            (mul_nonneg (le_max_right _ _) hp)
      _ = max C 0 * Real.sqrt 2 * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionSectionL2Norm d n f := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
