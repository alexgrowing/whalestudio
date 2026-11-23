import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.BaseSt
import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.MinfUnique

noncomputable section

open Formalism.BasicNotions MeasureTheory

namespace Formalism.IndefR.Eqv

theorem minfDensity_ne_zero (N : ℕ) : Formalism.L2.Theta.minfDensity N ≠ 0 := by
  unfold Formalism.L2.Theta.minfDensity
  exact ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)

theorem minfDensity_ne_top (N : ℕ) : Formalism.L2.Theta.minfDensity N ≠ ⊤ := by
  unfold Formalism.L2.Theta.minfDensity
  exact ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero)

theorem minfExUnique_of (h : Formalism.IndefR.Leaf.MinfExistsUnique) : MinfExUnique :=
  fun p q => h p q _ (minfDensity_ne_zero (p + q)) (minfDensity_ne_top (p + q))

end Formalism.IndefR.Eqv

end
