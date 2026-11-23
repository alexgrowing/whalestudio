import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem ShOfPower.pderiv_lineClass (d : IndexData) (u : Idx d → ℚ) (p : Idx d) :
    pderiv p (lineClass d u) = C (-u p) := by
  classical
  unfold lineClass lamDotX
  rw [map_neg, map_sum]
  simp only [pderiv_C_mul]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp [pderiv_X_of_ne hq]
  · simp

theorem ShOfPower.pderiv_lineClass_pow (d : IndexData) (u : Idx d → ℚ) (p : Idx d) :
    pderiv p (lineClass d u ^ (d.D + 1)) =
      C (-((d.D + 1 : ℕ) : ℚ) * u p) * lineClass d u ^ d.D := by
  rw [pderiv_pow, ShOfPower.pderiv_lineClass, Nat.add_sub_cancel]
  simp only [map_mul, map_neg, map_natCast]
  ring

theorem ShOfPower.proof : ShOfPower.Statement := by
  intro d τ u
  have hs : ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j),
        pderiv (τ, i) (lineClass d u ^ (d.D + 1)) =
      C (-((d.D + 1 : ℕ) : ℚ) * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), u (τ, i)) *
        lineClass d u ^ d.D := by
    rw [Finset.mul_sum, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => ShOfPower.pderiv_lineClass_pow d u (τ, i))
  unfold shiftFl degAt
  rw [hs, C_mul', LinearMap.map_smul, smul_eq_mul]
  ring

end GroundTheory.Heights₂.Heights.TheoremB
