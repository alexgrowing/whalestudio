import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCoordinatePartialDerivationComm
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreCoordinatePartialDerivation_comm : ∀ (I : Type) [Fintype I] (g : ℕ) (W : Opens (Tot I g)) (a b : Fin g) (x : Hol W), dw a (dw b x) = dw b (dw a x) := by
  first | exact @GlobalTheory.AnPer.dw_comm | exact GlobalTheory.AnPer.dw_comm | (intros; apply GlobalTheory.AnPer.dw_comm <;> assumption)
