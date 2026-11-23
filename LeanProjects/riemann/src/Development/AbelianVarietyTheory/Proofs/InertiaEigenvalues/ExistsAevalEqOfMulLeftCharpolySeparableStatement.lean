import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfMulLeftCharpolySeparable
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_aeval_eq_of_mulLeft_charpoly_separable : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → ∀ x : A, ∃ p : E[X], aeval g p = x := by
  first | exact @GlobalTheory.SepGenElt.exists_aeval_eq | exact GlobalTheory.SepGenElt.exists_aeval_eq | (intros; apply GlobalTheory.SepGenElt.exists_aeval_eq <;> assumption)
