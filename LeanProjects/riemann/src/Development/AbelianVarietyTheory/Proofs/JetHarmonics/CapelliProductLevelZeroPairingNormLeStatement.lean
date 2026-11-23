import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingNormLe
import Formalism.HermitianCurvature.StatementTBB
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliProduct_levelZeroPairing_norm_le : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (A : ℝ), B.AB k r ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Z : B.Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ), B.CkOn ⊤ (B.GV k r) X → B.CCle A (5 + w.length * (2 * r + k + 1)) X c → B.CCle A 5 Z c' → ‖B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z‖ ≤ C * c * c' := by
  first | exact @GlobalTheory.beta_capelliFold_norm_le | exact GlobalTheory.beta_capelliFold_norm_le | (intros; apply GlobalTheory.beta_capelliFold_norm_le <;> assumption)
