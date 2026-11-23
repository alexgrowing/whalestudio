import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConePow

theorem cupPowC_smul {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)
    (z : CH.Cn (CH.modF A) 2) (a : R) (k : ℕ) : cupPowC A (a • z) k = a ^ k • cupPowC A z k := by
  induction k with
  | zero => rw [pow_zero, one_smul]; rfl
  | succ k ih =>
    change (CH.mulP A).cupC (by omega) (cupPowC A (a • z) k) (a • z) =
      a ^ (k + 1) • (CH.mulP A).cupC (by omega) (cupPowC A z k) z
    rw [ih, map_smul, map_smul, LinearMap.smul_apply, pow_succ', mul_smul]

end GlobalTheory.CompanionTheory.ConePow
