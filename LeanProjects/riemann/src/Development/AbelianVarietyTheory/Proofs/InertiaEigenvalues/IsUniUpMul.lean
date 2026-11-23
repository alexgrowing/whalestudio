import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.CylinderCountFamily
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JCountP
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists

namespace GlobalTheory.UnipotentUpperMul

theorem isUniUp_mul : ∀ {R : Type} [inst : CommRing R] {N : ℕ} {M M' : Matrix (Fin N) (Fin N) R},
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp M → Formalism.MainNotions.ArithmeticCylinders.IsUniUp M' → Formalism.MainNotions.ArithmeticCylinders.IsUniUp (M * M') := by
  intro R _ N M M' hM hM' a b
  constructor
  · intro hba
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k a with hka | hak
    · rw [(hM a k).1 hka, zero_mul]
    · rw [(hM' k b).1 (lt_of_lt_of_le hba hak), mul_zero]
  · intro hab
    subst hab
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(hM a a).2 rfl, (hM' a a).2 rfl, mul_one]
    · intro k _ hka
      rcases lt_or_gt_of_ne hka with h | h
      · rw [(hM a k).1 h, zero_mul]
      · rw [(hM' k a).1 h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

end GlobalTheory.UnipotentUpperMul
