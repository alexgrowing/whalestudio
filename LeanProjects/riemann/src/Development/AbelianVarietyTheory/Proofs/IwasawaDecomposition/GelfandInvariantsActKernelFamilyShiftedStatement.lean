import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantsActKernelFamilyShifted
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandInvariants_act_kernelFamily_shifted : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ (Y M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (Y → GA D V → ℂ)), (∀ f y, κ f y ∈ SmFun θ V) → ∀ (τ : D.what₂.Tau) (Q : Matrix (Fin V.rank) (Fin V.rank) ℂ →ₗ[ℂ] Module.End ℂ M), Formalism.REAL.GlRel (fun i j => Q (Matrix.single i j 1)) → (∀ X ∈ lieAt V τ, ∃ lam : ℂ, ∀ f y g, HasDerivAt (fun t : ℝ => κ f y (g * oneP θ V τ X t)) (κ (Q X f + lam • f) y g) 0) → ∃ c : ℂ, ∀ k f y, gelf θ V τ k (κ f y) = κ (GlobalTheory.SmoothForms.gelfA (fun i j => Q (Matrix.single i j 1) + if i = j then algebraMap ℂ (Module.End ℂ M) c else 0) k f) y := by
  first | exact @GlobalTheory.Mem.Lift.OneSide.gelf_kernel | exact GlobalTheory.Mem.Lift.OneSide.gelf_kernel | (intros; apply GlobalTheory.Mem.Lift.OneSide.gelf_kernel <;> assumption)
