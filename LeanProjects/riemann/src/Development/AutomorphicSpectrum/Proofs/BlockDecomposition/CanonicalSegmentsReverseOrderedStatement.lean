import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalSegmentsReverseOrdered
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_segments_reverse_ordered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k), IsCanon Γ → IsRevOrdered Γ := by
  first | exact @GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon | exact GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon | (intros; apply GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon <;> assumption)
