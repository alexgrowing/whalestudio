import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleOfContragredientSocle
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosocle_of_contragredient_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ τ' : IrrRep (GL (Fin N) k), IsSocle τ'.ρ (contra π) → ∃ τ : IrrRep (GL (Fin N) k), IsCosocle τ.ρ π := by
  first | exact @GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra | exact GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra | (intros; apply GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra <;> assumption)
