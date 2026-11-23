import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightsOfExtension
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weights_of_extension : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → (∀ (μ : Fin n → ℝ) (v : H), v ≠ 0 → (IsWtOn (Kset ε) π μ v ↔ ∑ a, μ a = (m : ℝ) ∧ IsWtS π' (fun a => μ a - (m : ℝ) / n) v)) ∧ ∀ (lam Λ : Fin n → ℝ) (c : ℝ) (S : Submodule ℂ H), IsKTypeU ε lam π Λ S ↔ ∑ a, Λ a = (m : ℝ) ∧ IsKTypeS ε (fun a => lam a - c) π' (fun a => Λ a - (m : ℝ) / n) S := by
  first | exact @GlobalTheory.SUWt.wt_ktype_ext | exact GlobalTheory.SUWt.wt_ktype_ext | (intros; apply GlobalTheory.SUWt.wt_ktype_ext <;> assumption)
