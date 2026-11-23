import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralClosureFgDvrOfSeparableCharpoly
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_fg_dvr_of_separable_charpoly : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  first | exact @GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly | exact GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly | (intros; apply GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly <;> assumption)
