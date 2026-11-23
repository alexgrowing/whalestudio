import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

namespace GlobalTheory.SquareEqNegReIm

theorem re_im_of_sq_eq_neg {z : ℂ} {c : ℝ} (hc : 0 ≤ c) (hz : z ^ 2 = -(c : ℂ)) :
    z.re = 0 ∧ z.im ^ 2 = c := by
  have hs : ((Real.sqrt c : ℝ) : ℂ) ^ 2 = (c : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hc]
  have h : z ^ 2 = (((Real.sqrt c : ℝ) : ℂ) * Complex.I) ^ 2 := by
    rw [mul_pow, hs, Complex.I_sq, hz]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · rw [h]; simp [Real.sq_sqrt hc]
  · rw [h]; simp [Real.sq_sqrt hc]

theorem re_eq_zero_and_im_sq {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    H.rt0.re = (0 : ℝ) ∧ H.rt0.im ^ (2 : ℕ) = (H.d : ℝ) := by
  refine re_im_of_sq_eq_neg (by positivity) ?_
  rw [H.sqrt_neg_disc_sq]; simp

end GlobalTheory.SquareEqNegReIm
