import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentDualPrecedesIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_dual_precedes_iff : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ Δ' : Segment k), (segDual Δ).Precedes (segDual Δ') ↔ Δ'.Precedes Δ := by
  first | exact @GlobalTheory.CompanionTheory.SegDualPrec.segDual_precedes | exact GlobalTheory.CompanionTheory.SegDualPrec.segDual_precedes | (intros; apply GlobalTheory.CompanionTheory.SegDualPrec.segDual_precedes <;> assumption)
