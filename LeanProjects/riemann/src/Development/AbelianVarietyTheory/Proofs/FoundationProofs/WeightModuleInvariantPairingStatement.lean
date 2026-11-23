import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeightModuleInvariantPairing
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_module_invariant_pairing : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ) (lam : ι → DomWeight n), (∀ τ a, (lam τ).w a = (mu τ a : ℤ) + sh τ) → ∃ B : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] NablaT ℂ n mu →ₗ[ℂ] ℂ, (∀ u, u ≠ 0 → ∃ v, B v u ≠ 0) ∧ ∀ (g : ι → GL (Fin n) ℂ) v u, B (Formalism.L2.DIV.rhoK lam g v) (wtOp ℂ n mu sh g u) = B v u := by
  first | exact @GlobalTheory.AutPairing.exists_invariant_pairing | exact GlobalTheory.AutPairing.exists_invariant_pairing | (intros; apply GlobalTheory.AutPairing.exists_invariant_pairing <;> assumption)
