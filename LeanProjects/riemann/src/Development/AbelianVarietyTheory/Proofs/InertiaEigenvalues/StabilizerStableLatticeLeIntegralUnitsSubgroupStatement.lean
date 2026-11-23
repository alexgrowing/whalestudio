import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerStableLatticeLeIntegralUnitsSubgroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup : ∀ (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A] (g : A) (L : stLat O E g), MulAction.stabilizer Aˣ L ≤ intUnits O A := by
  first | exact @GlobalTheory.UnitLemma.stabilizer_le_intUnits | exact GlobalTheory.UnitLemma.stabilizer_le_intUnits | (intros; apply GlobalTheory.UnitLemma.stabilizer_le_intUnits <;> assumption)
