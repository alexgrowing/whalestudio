import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_class_cuspidal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k), x.IsCusp → (dualCl x).IsCusp ∧ (dualCl x).1 = x.1 := by
  first | exact @GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp | exact GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp | (intros; apply GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp <;> assumption)
