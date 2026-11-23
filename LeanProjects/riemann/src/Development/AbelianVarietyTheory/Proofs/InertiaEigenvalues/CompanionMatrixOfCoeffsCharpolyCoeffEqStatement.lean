import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompanionMatrixOfCoeffsCharpolyCoeffEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.companionMatrixOfCoeffs_charpoly_coeff_eq : ∀ (k : Type) [CommRing k] (r : ℕ) (p : Fin r → k) (i : Fin r), (companion p).charpoly.coeff (i : ℕ) = p i := by
  first | exact @GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring | exact GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring | (intros; apply GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring <;> assumption)
