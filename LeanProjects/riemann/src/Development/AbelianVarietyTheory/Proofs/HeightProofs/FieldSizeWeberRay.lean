import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberLeAbsDiscrOfFinrankEqTwo
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulFinrankMemDifferentIdeal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeckeIdealEqOfRay
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LogRootDiscrLeOfNatCastMemDifferentIdeal
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem log_sizes_of_isRay_natCast (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M]
    [NumberField M] [Algebra K M] [IsAbelianGalois K M] (h2 : Module.finrank ℚ K = 2) (n : ℕ) (hn : 0 < n)
    (hR : IsRay M (Ideal.span {(n : 𝓞 K)})) :
    Real.log (Module.finrank ℚ M) ≤ Real.log (8 * |(discr K : ℝ)|) + 2 * Real.log n ∧
      Real.log |((discr M : ℤ) : ℝ)| / Module.finrank ℚ M ≤
        Real.log (4 * |(discr K : ℝ)|) + Real.log |(discr K : ℝ)| / 2 + 3 * Real.log n := by
  have hq : Ideal.span {(n : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne'
  have hE : IsEmpty (K →+* ℝ) := ⟨fun φ =>
    IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ) (by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      simp)⟩
  have h1 := GlobalTheory.FieldSize.RayDegree.finrank_le K M _ hq hR
  rw [Fintype.card_eq_zero, pow_zero, mul_one, Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2] at h1
  have hcl := GlobalTheory.classNumber_le_four_mul_abs_discr K h2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero K)
  have hr : 0 < Module.finrank K M := Module.finrank_pos
  have hr' : (0 : ℝ) < Module.finrank K M := by exact_mod_cast hr
  have h3 : (Module.finrank K M : ℝ) ≤ 4 * |(discr K : ℝ)| * (n : ℝ) ^ 2 := by
    have : (Module.finrank K M : ℝ) ≤ (classNumber K : ℝ) * (n : ℝ) ^ 2 := by exact_mod_cast h1
    exact this.trans (mul_le_mul_of_nonneg_right hcl (by positivity))
  have h4 : (Module.finrank ℚ M : ℝ) = 2 * Module.finrank K M := by
    rw [← Module.finrank_mul_finrank ℚ K M, h2]; push_cast; ring
  have h5 := Real.log_le_log hr' h3
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h5
  refine ⟨?_, ?_⟩
  · rw [h4, show 8 * |(discr K : ℝ)| = 2 * (4 * |(discr K : ℝ)|) by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (x := 2) (by positivity) (by positivity)]
    push_cast at h5
    linarith
  · have h6 := GlobalTheory.DifferentBound.natCast_mul_finrank_mem_differentIdeal K M n hn (fun 𝔭 h => hR.1 𝔭 (fun hd => h (by
      rwa [Ideal.dvd_span_singleton] at hd)))
    have h7 := GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal K M _ (Nat.mul_pos hn hr) h6
    rw [h2, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)] at h7
    push_cast at h5 h7
    linarith

end GlobalTheory.FieldSize
