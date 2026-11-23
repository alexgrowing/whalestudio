import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestTypeParameterAscent
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_type_parameter_ascent : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → ∀ lam' : Fin n → ℝ, IsParS lam' → (∃ S : Submodule ℂ H, IsKTypeS ε lam' π' (lowCh ε lam') S) → IsParU (fun a => lam' a + (m : ℝ) / n) ∧ ∑ a, (lam' a + (m : ℝ) / n) = (m : ℝ) := by
  first | exact @GlobalTheory.SuVPar.parS_lifts | exact GlobalTheory.SuVPar.parS_lifts | (intros; apply GlobalTheory.SuVPar.parS_lifts <;> assumption)
