import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCanonicalSegmentOrder
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_segment_order : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k), ∃ σ : Equiv.Perm (Fin h), IsCanon (Γ ∘ σ) := by
  first | exact @GlobalTheory.CompanionTheory.CanonOrder.exists_isCanon | exact GlobalTheory.CompanionTheory.CanonOrder.exists_isCanon | (intros; apply GlobalTheory.CompanionTheory.CanonOrder.exists_isCanon <;> assumption)
