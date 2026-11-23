import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BirationalYPt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsFurther
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantShift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsSemipositiveRelConstShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ArithmeticVolumeDimensionOne.proof (hG6 : ArithmeticVolumeBigDimensionOne.Statement) : ArithmeticVolumeDimensionOne.Statement := by
  intro K _ ι _ Ω _ _ y M P0 II hII har hb hM hpos
  set T := II K ι (mCoordIdeal y) 1 (fun _ => M)
  set g := geomDeg (mCoordIdeal y) M 0
  have hden : 0 < 2 * (|g| + 1) := by positivity
  set η := T / (2 * (|g| + 1))
  have hη0 : 0 < η := div_pos hpos hden
  have he : η * (2 * (|g| + 1)) = T := div_mul_cancel₀ T hden.ne'
  have hηlt : η * g < T := by
    have h1 : η * g ≤ η * |g| := mul_le_mul_of_nonneg_left (le_abs_self g) hη0.le
    nlinarith
  have hshift := ConstantShift.proof K ι (II K ι) (mCoordIdeal y) 0 M η (hII K ι) har hM.semipos.1
  have hpos' : 0 < II K ι (mCoordIdeal y) 1 (fun _ => HermLine.constShift M η) := by
    have e : II K ι (mCoordIdeal y) 1 (fun _ => HermLine.constShift M η) = T - ((0 : ℕ) + 1 : ℝ) * η * g :=
      hshift
    rw [e]
    push_cast
    linarith
  have hvol := hG6 K ι Ω y (HermLine.constShift M η) P0 II hII har hb hM.normalForm_baseLattice_le_dualSpan_sup_line
    (isSemipositiveRel_constShift hM.semipos η) (by rw [constShift_a]; exact hM.nef)
    (isConjInvariantH_constShift hM.conjInv η)
  obtain ⟨n, hn, s, hs, hs0, hsmall⟩ := exists_small_section_of_arithmeticVolume_pos (hpos'.trans_le hvol)
  have hn' : (0 : ℝ) < n * η := mul_pos (by exact_mod_cast hn) hη0
  refine ⟨n, s, hn, by rwa [constShift_a] at hs, hs0, Real.exp (-(n * η)), ?_, ?_⟩
  · rw [Real.exp_lt_one_iff]
    linarith
  · intro dg dh g' h z hg hh hdeg heq hz
    have hle := hsmall dg dh g' h z hg hh (by rw [constShift_a]; exact hdeg) heq hz
    have e : Real.exp (-(n * η)) = Real.exp (-η) ^ n := by
      rw [← Real.exp_nat_mul]
      ring_nf
    refine hle.trans (le_of_eq ?_)
    rw [constShift_h, mul_pow, e]
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
