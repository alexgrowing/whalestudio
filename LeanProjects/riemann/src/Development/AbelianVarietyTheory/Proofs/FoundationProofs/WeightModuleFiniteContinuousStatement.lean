import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeightModuleFiniteContinuous
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_module_finite_continuous : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ), (∀ τ, FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)))) ∧ FiniteDimensional ℂ (NablaT ℂ n mu) ∧ ∀ (u : NablaT ℂ n mu) (ℓ : Module.Dual ℂ (NablaT ℂ n mu)), Continuous fun g : ι → GL (Fin n) ℂ => ℓ (wtOp ℂ n mu sh g u) := by
  first | exact @GlobalTheory.WtCont.finite_continuous_wtOp | exact GlobalTheory.WtCont.finite_continuous_wtOp | (intros; apply GlobalTheory.WtCont.finite_continuous_wtOp <;> assumption)
