import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormExpCharacterSingle
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_exp_character_single : ∀ {F : Type} [Field F] [NumberField F] {n r : ℕ} (s : Fin r → ℂ) (k : Fin r) (c : ℝ), ‖expChar F n s (Pi.single k c)‖ = Real.exp (2 * Module.finrank ℚ F * c * ((s k).re - (negRho n r k).re)) := by
  first | exact @GlobalTheory.TorusExp.norm_expChar_single | exact GlobalTheory.TorusExp.norm_expChar_single | (intros; apply GlobalTheory.TorusExp.norm_expChar_single <;> assumption)
