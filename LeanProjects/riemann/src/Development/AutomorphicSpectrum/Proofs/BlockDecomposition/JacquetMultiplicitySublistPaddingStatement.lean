import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySublistPadding
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityDropZeroBlocksStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_sublist_padding : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (W : List (IrrGL k)) (c : Fin W.length → Fin h) (i : Fin h) (Y : Fin W.length → IrrGL k), (∀ j, c j = i → Y j = W.get j) → (∀ j, c j ≠ i → (Y j).1 = 0) → ∀ (hd : ∑ j, (Y j).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), jm Y hd π = jmL (sub W c i) π := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.jm_row | exact GlobalTheory.CompanionTheory.FineProd.jm_row | (intros; apply GlobalTheory.CompanionTheory.FineProd.jm_row <;> assumption)
