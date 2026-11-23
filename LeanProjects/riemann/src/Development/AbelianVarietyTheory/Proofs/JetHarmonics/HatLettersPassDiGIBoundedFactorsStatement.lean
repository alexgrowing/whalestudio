import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersPassDiGIBoundedFactors
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hatLetters_pass_Di_gI_boundedFactors : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → (∀ X ∈ hats d.L, X * d.L.Di ∈ nfSpan d (hats d.L) 1 0 1 ∧ X * TL.gI d.L ∈ nfSpan d (hats d.L) 0 1 1) ∧ (∀ b ∈ bmon d, (∀ f ∈ d.L.fns, Commute b f) ∧ Commute b d.L.Di ∧ Commute b (TL.gI d.L) ∧ star b ∈ bmon d) ∧ Commute d.L.Di (TL.gI d.L) := by
  first | exact @GlobalTheory.HatNF.Den.hat_den | exact GlobalTheory.HatNF.Den.hat_den | (intros; apply GlobalTheory.HatNF.Den.hat_den <;> assumption)
