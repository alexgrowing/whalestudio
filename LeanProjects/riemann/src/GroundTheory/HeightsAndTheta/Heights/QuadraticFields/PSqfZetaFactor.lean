import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.Quadratic
import GroundTheory.GlobalFields.AnalyticClassNumber.QuadraticConductor
import GroundTheory.HeightsAndTheta.Heights.QuadraticFields.SqfDiscr
import GroundTheory.HeightsAndTheta.Heights.QuadraticFields.SqfZetaFactor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Rows

theorem jacobiSym_neg_eq_of_mod_four {p d : ℕ} (hp : Odd p) (hd4 : d % 4 = 3) :
    jacobiSym (-(d : ℤ)) p = jacobiSym p d := by
  rw [jacobiSym.neg _ hp]
  have hdo : Odd d := Nat.odd_iff.mpr (by omega)
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hp) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four' hdo h]
  · rw [ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four hd4 h]
    ring

theorem SqfZetaFactor.proof (h₁ : SqfDiscr.Statement) : SqfZetaFactor.Statement := by
  intro d _ hsq hd4 χ hχ K _ _ hK ⟨x, hx⟩ s hs
  have : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := hK }
  have hdisc : NumberField.discr K = -(d : ℤ) := h₁ d hsq hd4 K hK x hx
  have hD : (NumberField.discr K).natAbs = d := by rw [hdisc]; simp
  rw [GroundTheory.Global.Quadratic.dedekindZeta_eq_mul K hs,
    ← GroundTheory.Global.Quadratic.LFunction_kroneckerChar K s,
    ← GroundTheory.Global.Quadratic.LFunction_changeLevel_of_eq hD]
  congr 2
  refine MulChar.ext fun a => ?_
  obtain ⟨p, hp_gt, hpp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod a.isUnit (2 * d)
  have := Fact.mk hpp
  have hp2 : p ≠ 2 := by omega
  rw [← hpa, GroundTheory.Global.Quadratic.changeLevel_of_eq_apply hD,
    GroundTheory.Global.Quadratic.kroneckerChar_apply_prime K p hp2, hdisc, hχ p,
    jacobiSym.legendreSym.to_jacobiSym, jacobiSym_neg_eq_of_mod_four (hpp.odd_of_ne_two hp2) hd4]

end GroundTheory.Heights₂.Heights.Rows
