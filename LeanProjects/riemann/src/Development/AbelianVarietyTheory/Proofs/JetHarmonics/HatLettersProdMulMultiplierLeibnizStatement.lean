import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersProdMulMultiplierLeibniz
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hatLetters_prod_mul_multiplier_leibniz : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ H : List A, (∀ h ∈ H, h ∈ hats L) → ∃ ts : List (ℕ × ℂ × List A), (∀ t ∈ ts, t.1 ≤ H.length * (r + 1) ∧ t.2.2.length = H.length ∧ ∀ h ∈ t.2.2, h ∈ hats L) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, H.prod * m q = (ts.map fun t => t.2.1 • (m (q + t.1) * t.2.2.prod)).sum := by
  first | exact @GlobalTheory.HatNF.prod_hats_mul_multiplier | exact GlobalTheory.HatNF.prod_hats_mul_multiplier | (intros; apply GlobalTheory.HatNF.prod_hats_mul_multiplier <;> assumption)
