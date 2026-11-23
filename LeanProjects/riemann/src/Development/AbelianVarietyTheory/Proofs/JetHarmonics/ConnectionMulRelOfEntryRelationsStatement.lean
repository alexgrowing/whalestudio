import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConnectionMulRelOfEntryRelations
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connection_mulRel_of_entry_relations : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ m : ℕ → A, (∀ q, (∀ f ∈ d.L.fns, Commute f (m q)) ∧ (∀ l, d.L.p l * m q = m q * d.L.p l + m (q + 1)) ∧ (∀ l, d.L.pb l * m q = m q * d.L.pb l + m (q + 1)) ∧ (∀ f : M.Ty P → ℂ, Commute (d.κ f) (m q)) ∧ star (m q) = m q ∧ ∀ Y : ℝ, d.QQ Y 1 0 * m q = m q * d.QQ Y 1 0 - d.L.ζb * d.L.GGi * m (q + 1) * d.QQ Y 1 1) → MulRel d.L m := by
  first | exact @GlobalTheory.HatNF.MulRelAlg.mulRel_of_entries | exact GlobalTheory.HatNF.MulRelAlg.mulRel_of_entries | (intros; apply GlobalTheory.HatNF.MulRelAlg.mulRel_of_entries <;> assumption)
