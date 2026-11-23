import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLetterMulBoundedFactorMemNormalFormSpan
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hatLetter_mul_boundedFactor_mem_normalFormSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ X ∈ hats d.L, ∀ b ∈ bmon d, X * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.hats_mul_bmon_mem_nfSpan | exact GlobalTheory.HatNF.hats_mul_bmon_mem_nfSpan | (intros; apply GlobalTheory.HatNF.hats_mul_bmon_mem_nfSpan <;> assumption)
