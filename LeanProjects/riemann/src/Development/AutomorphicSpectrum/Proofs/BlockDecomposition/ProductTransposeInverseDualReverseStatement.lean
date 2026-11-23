import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_transpose_inverse_dual_reverse : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k → ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), ∃ hd' : ∑ a, (dualCl (x (Fin.rev a))).1 = N, Nonempty (Representation.Equiv ((prodIrr x hd).comp (thetaW k N)) (prodIrr (fun a => dualCl (x (Fin.rev a))) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaProd.prodIrr_comp_thetaW | exact GlobalTheory.CompanionTheory.ThetaProd.prodIrr_comp_thetaW | (intros; apply GlobalTheory.CompanionTheory.ThetaProd.prodIrr_comp_thetaW <;> assumption)
