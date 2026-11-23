import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanContragredient
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_kazhdan_contragredient : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GKLocal k → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → Nonempty (Representation.Equiv (π.comp (thetaW k N)) (contra π)) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra | exact GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra | (intros; apply GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra <;> assumption)
