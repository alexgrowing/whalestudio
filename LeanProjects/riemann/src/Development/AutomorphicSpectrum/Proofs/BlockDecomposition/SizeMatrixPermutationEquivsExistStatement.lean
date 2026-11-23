import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeMatrixPermutationEquivsExist
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_matrix_permutation_equivs_exist : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {l c : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k) (e : Fin c ≃ Fin l), (∀ a, y a = x (e a)) → ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)), (∀ i j, b.1 i j = if e j = i then (x i).1 else 0) → ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1), jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CellBij.jhMult_cell_bij | exact GlobalTheory.CompanionTheory.CellBij.jhMult_cell_bij | (intros; apply GlobalTheory.CompanionTheory.CellBij.jhMult_cell_bij <;> assumption)
