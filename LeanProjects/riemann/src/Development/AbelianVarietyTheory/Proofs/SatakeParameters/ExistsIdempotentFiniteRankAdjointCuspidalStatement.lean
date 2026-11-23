import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdempotentFiniteRankAdjointCuspidal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_finiteRank_adjoint_cuspidal : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a), ∃ P : Module.End ℂ π.V, P ≠ 0 ∧ P ∘ₗ P = P ∧ FiniteDimensional ℂ (LinearMap.range P) ∧ ∀ s : Op L a → Op L a, (s = invTOp ∨ s = conjOp) → ∀ B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B (π.op (.fin k) φ) (π.op (s (.fin k)) ψ) = B φ ψ) → (∀ k φ ψ, B (π.op (.cpt k) φ) (π.op (s (.cpt k)) ψ) = B φ ψ) → (∀ X φ ψ, B (π.op (.lie X) φ) ψ + B φ (π.op (s (.lie X)) ψ) = 0) → ∃ P' : Module.End ℂ π.V, ∀ φ ψ, B (P φ) ψ = B φ (P' ψ) := by
  first | exact @GlobalTheory.IdemAdj.exists_idem_adj | exact GlobalTheory.IdemAdj.exists_idem_adj | (intros; apply GlobalTheory.IdemAdj.exists_idem_adj <;> assumption)
