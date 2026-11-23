import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcat
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_concat : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s N : ℕ} (y : Fin s → IrrGL k) (hy : ∑ a, (y a).1 = N) (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL k) (hx : ∀ a, ∑ i, (x a i).1 = (y a).1) (hcat : ∑ i, (concat c x i).1 = N) (hpos : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hfl : HasFiniteLength π), jm y hy π ≤ jm (concat c x) hcat π := by
  first | exact @GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat | exact GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat | (intros; apply GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat <;> assumption)
