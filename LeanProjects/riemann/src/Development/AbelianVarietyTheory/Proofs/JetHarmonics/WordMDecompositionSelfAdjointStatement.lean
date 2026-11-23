import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordMDecompositionSelfAdjoint
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_m_decomposition_self_adjoint : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ Y ∈ (ofWord L st w).inv, star Y = Y → Y - 1 ∈ (ofWord L st w).inv → ∃ E : SlopeTestRemainingChoices S A, (∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0) ∧ (ofWord L st w).m L Y = io (d.L.m0 Y) + io (d.L.ζ * d.L.ζbi * d.L.GGi) * E := by
  first | exact @GlobalTheory.HatNF.MShapeNF.mshape | exact GlobalTheory.HatNF.MShapeNF.mshape | (intros; apply GlobalTheory.HatNF.MShapeNF.mshape <;> assumption)
