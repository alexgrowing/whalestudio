import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

namespace GlobalTheory

theorem siegel_two_im_quad_nonneg {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) (hT : GlobalTheory.IsSiegel T)
    (x : Fin g → ℂ) :
    (∑ a, ∑ c, ((2 : ℂ) • T.map fun t => (t.im : ℂ)) a c * (starRingEnd ℂ (x a) * x c)).im = 0 ∧
    0 ≤ (∑ a, ∑ c, ((2 : ℂ) • T.map fun t => (t.im : ℂ)) a c * (starRingEnd ℂ (x a) * x c)).re := by
  have hP : (T.map Complex.im).PosDef := hT.2
  have hs : ∀ a c, (T a c).im = (T c a).im := by
    intro a c
    have := congrFun (congrFun hP.isHermitian c) a
    simpa [Matrix.conjTranspose_apply] using this
  have hq : ∀ v : Fin g → ℝ, 0 ≤ ∑ a, ∑ c, (T a c).im * (v a * v c) := by
    intro v
    have := hP.posSemidef.dotProduct_mulVec_nonneg v
    simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum] at this
    refine this.trans_eq ?_
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  constructor
  · have h1 : (∑ a, ∑ c, ((2 : ℂ) • T.map fun t => (t.im : ℂ)) a c * (starRingEnd ℂ (x a) * x c)).im
        = ∑ a, ∑ c, 2 * (T a c).im * ((x a).re * (x c).im) - ∑ a, ∑ c, 2 * (T a c).im * ((x a).im * (x c).re) := by
      rw [← Finset.sum_sub_distrib, Complex.im_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_sub_distrib, Complex.im_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp
      ring
    rw [h1, sub_eq_zero, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hs c a]; ring
  · have h1 : (∑ a, ∑ c, ((2 : ℂ) • T.map fun t => (t.im : ℂ)) a c * (starRingEnd ℂ (x a) * x c)).re
        = 2 * (∑ a, ∑ c, (T a c).im * ((x a).re * (x c).re)) + 2 * ∑ a, ∑ c, (T a c).im * ((x a).im * (x c).im) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Complex.re_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp
      ring
    rw [h1]
    have := hq fun a => (x a).re
    have := hq fun a => (x a).im
    positivity

end GlobalTheory
