import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_class_twist_neg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s) := by
  first | exact @GlobalTheory.CompanionTheory.ZcDual.dualCl_nu | exact GlobalTheory.CompanionTheory.ZcDual.dualCl_nu | (intros; apply GlobalTheory.CompanionTheory.ZcDual.dualCl_nu <;> assumption)
