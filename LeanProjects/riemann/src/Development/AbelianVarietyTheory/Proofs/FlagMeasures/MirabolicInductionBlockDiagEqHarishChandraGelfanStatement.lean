import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionBlockDiagEqHarishChandraGelfan
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicInduction_blockDiag_eq_harishChandra_gelfandGraev : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i k : ℕ) (ρ : Gn g i → ℂ), i ≤ k → IsClass ρ → ∀ h : Gn g k, indR ψ i (k + 1) ρ (diag1 h (k + 1)) = hc i (k - i) ρ (gg ψ (k - i)) k h := by
  first | exact @GlobalTheory.GLm.indR_diag1_eq_hc_gg | exact GlobalTheory.GLm.indR_diag1_eq_hc_gg | (intros; apply GlobalTheory.GLm.indR_diag1_eq_hc_gg <;> assumption)
