import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlaceFlagUnipotentRadicalIsUnipotent
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NGClosed
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceFlagUnipotentRadical_isUnipotent : ∀ {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Formalism.REAL.UJ ε), g ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc ε e z → (Formalism.MainNotions.S.uMat g - 1) ^ (2 * r + 1) = 0 := by
  first | exact @GlobalTheory.unipRad_pow_eq_zero | exact GlobalTheory.unipRad_pow_eq_zero | (intros; apply GlobalTheory.unipRad_pow_eq_zero <;> assumption)
