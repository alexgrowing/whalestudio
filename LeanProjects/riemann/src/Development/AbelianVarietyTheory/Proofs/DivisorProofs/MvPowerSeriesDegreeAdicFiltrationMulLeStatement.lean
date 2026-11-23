import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesDegreeAdicFiltrationMulLe
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeriesDegreeAdicFiltration_mul_le : ∀ (σ R : Type) [CommRing R] (I : Ideal R) (j k : ℕ), filt (σ := σ) I j * filt I k ≤ filt I (j + k) := by
  first | exact @GlobalTheory.FormalOrigin.Extend.filt_mul_filt_le | exact GlobalTheory.FormalOrigin.Extend.filt_mul_filt_le | (intros; apply GlobalTheory.FormalOrigin.Extend.filt_mul_filt_le <;> assumption)
