import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CRSecA

noncomputable section

open Matrix Set Filter Topology
open scoped ComplexOrder ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CRSec

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.LVs.HolB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def reL : Mn n →L[ℝ] Mn n := (1 / 2 : ℂ) • (ContinuousLinearMap.id ℝ (Mn n) + cT)

def imL : Mn n →L[ℝ] Mn n := (-(Complex.I / 2)) • (ContinuousLinearMap.id ℝ (Mn n) - cT)

theorem reL_apply (V : Mn n) : reL V = reP V := rfl

theorem imL_apply (V : Mn n) : imL V = imaginary V := rfl

theorem contDiff_fM (a0 : Mn n) : ContDiff ℝ ⊤ (fM a0) := by
  have h1 : ContDiff ℝ ⊤ (fun V : Mn n => (1 : Mn n) + imaginary V) := contDiff_const.add imL.contDiff
  unfold fM
  refine reL.contDiff.add (ContDiff.const_smul _ ?_)
  exact contDiff_mul' (contDiff_mul' (contDiff_mul' contDiff_const h1) h1) contDiff_const

theorem fM_line (a0 V0 dV : Mn n) (h0 : V0ᴴ = V0) (t : ℝ) :
    fM a0 (V0 + t • dV) = (V0 + Complex.I • (a0 * a0ᴴ)) +
      t • (reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ)) +
      (t ^ 2) • (Complex.I • (a0 * imaginary dV * imaginary dV * a0ᴴ)) := by
  have hr : reP (V0 + t • dV) = V0 + t • reP dV := by
    rw [← reL_apply, map_add, map_smul, reL_apply, reL_apply, reP_of_herm h0]
  have hi : imaginary (V0 + t • dV) = t • imaginary dV := by
    rw [← imL_apply, map_add, map_smul, imL_apply, imL_apply, imaginaryPart_of_isHermitian h0, zero_add]
  unfold fM
  rw [hr, hi]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    smul_add, smul_smul]
  module

theorem fderiv_fM (a0 V0 dV : Mn n) (h0 : V0ᴴ = V0) :
    fderiv ℝ (fM a0) V0 dV = reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ) := by
  have hd : DifferentiableAt ℝ (fM a0) V0 := ((contDiff_fM a0).differentiable (by simp)).differentiableAt
  have hl := ((hasDerivAt_id' (𝕜 := ℝ) (x := (0 : ℝ))).smul_const dV).const_add V0
  rw [one_smul] at hl
  have hd' : HasFDerivAt (fM a0) (fderiv ℝ (fM a0) V0) (V0 + (0 : ℝ) • dV) := by
    rw [zero_smul, add_zero]; exact hd.hasFDerivAt
  have hc := hd'.comp_hasDerivAt (0 : ℝ) hl
  have h1 := (hasDerivAt_id' (𝕜 := ℝ) (x := (0 : ℝ))).smul_const (reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ))
  have h2 := ((hasDerivAt_id' (𝕜 := ℝ) (x := (0 : ℝ))).pow 2).smul_const
    (Complex.I • (a0 * imaginary dV * imaginary dV * a0ᴴ))
  have h3 := ((hasDerivAt_const (0 : ℝ) (V0 + Complex.I • (a0 * a0ᴴ))).add h1).add h2
  simp only [one_smul, zero_add] at h3
  have h4 : HasDerivAt (fun t : ℝ => fM a0 (V0 + t • dV)) (reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ)) 0 := by
    refine (h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
    · simp only [fM_line a0 V0 dV h0 t, Pi.add_apply, Pi.pow_apply]
    · norm_num
  exact hc.unique h4

theorem herm_zero_of (H1 H2 : Mn n) (h1 : H1ᴴ = H1) (h2 : H2ᴴ = H2) (h : H1 + Complex.I • H2 = 0) :
    H1 = 0 ∧ H2 = 0 := by
  have hc : H1 - Complex.I • H2 = 0 := by
    have := congrArg conjTranspose h
    rw [conjTranspose_add, conjTranspose_smul, h1, h2, conjTranspose_zero] at this
    rw [sub_eq_add_neg, ← neg_smul]
    simpa using this
  have h2H1 : H1 + H1 = 0 := by
    calc H1 + H1 = (H1 + Complex.I • H2) + (H1 - Complex.I • H2) := by abel
      _ = 0 := by rw [h, hc, add_zero]
  have hH1 : H1 = 0 := by
    have : (2 : ℂ) • H1 = 0 := by rw [two_smul]; exact h2H1
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  refine ⟨hH1, ?_⟩
  rw [hH1, zero_add] at h
  exact (smul_eq_zero.mp h).resolve_left Complex.I_ne_zero

theorem fderiv_fM_inj (a0 V0 : Mn n) (h0 : V0ᴴ = V0) (ha : a0.det ≠ 0) :
    Function.Injective (fderiv ℝ (fM a0) V0) := by
  refine (injective_iff_map_eq_zero (fderiv ℝ (fM a0) V0)).2 fun dV hdV => ?_
  rw [fderiv_fM a0 V0 dV h0] at hdV
  have hH2 : (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ)ᴴ = a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_smul, imaginaryPart_isHermitian,
      Matrix.mul_assoc]
    simp
  obtain ⟨hr, hi⟩ := herm_zero_of _ _ (reP_herm dV) hH2 hdV
  have hu : IsUnit a0.det := isUnit_iff_ne_zero.mpr ha
  have huH : IsUnit a0ᴴ.det := by rw [det_conjTranspose]; exact (isUnit_iff_ne_zero.mpr ha).star
  have hB : (2 : ℂ) • imaginary dV = 0 := by
    have := congrArg (fun M => a0⁻¹ * M * (a0ᴴ)⁻¹) hi
    simp only [Matrix.mul_zero, Matrix.zero_mul] at this
    rw [← this, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huH, Matrix.mul_one,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have hB' : imaginary dV = 0 := (smul_eq_zero.mp hB).resolve_left two_ne_zero
  rw [← reP_add_imP dV, hr, hB', smul_zero, add_zero]

end PositivityTheory.Rg.Sw.HSt.CRSec
