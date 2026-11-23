import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_irreducible_tensor_decomposition : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s : ℕ} (d : Fin s → ℕ) (τ : IrrRep (Levi k fun a => Fin (d a))), ∃ σ : ∀ a, IrrCl (GL (Fin (d a)) k), Nonempty (τ.ρ.Equiv (piTensor fun a => (σ a).rep.ρ)) := by
  first | exact @GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor | exact GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor | (intros; apply GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor <;> assumption)
