import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentLengthTwoReducible
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_length_two_reducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible := by
  first | exact @GlobalTheory.CompanionTheory.BZReducible.cusp_times_nu_reducible | exact GlobalTheory.CompanionTheory.BZReducible.cusp_times_nu_reducible | (intros; apply GlobalTheory.CompanionTheory.BZReducible.cusp_times_nu_reducible <;> assumption)
