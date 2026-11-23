import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_lieAction_through_weylAlgebra : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ θ : InfF D, IsInfFam θ → ∃ x d : D.what₂.Tau → Fin T.rank × Fin S.rank → Module.End ℂ (GlobalTheory.RealWeil.thetaSub ψ S T), ∀ τ, IsCCR (x τ) (d τ) ∧ (∀ X ∈ lieAt T τ, ∃ lam : ℂ, ∀ f g h, HasDerivAt (fun t : ℝ => thKer ψ S T om f g (h * oneP θ T τ X t)) (thKer ψ S T om ((∑ i, ∑ j, X i j • ∑ a, x τ (i, a) * d τ (j, a)) f + lam • f) g h) 0) ∧ ∀ Y ∈ lieAt S τ, ∃ lam : ℂ, ∀ f g h, HasDerivAt (fun t : ℝ => thKer ψ S T om f (g * oneP θ S τ Y t) h) (thKer ψ S T om ((∑ a, ∑ b, Y a b • -∑ i, x τ (i, b) * d τ (i, a)) f + lam • f) g h) 0 := by
  first | exact @GlobalTheory.Mem.Lift.WeylAction.weyl_action | exact GlobalTheory.Mem.Lift.WeylAction.weyl_action | (intros; apply GlobalTheory.Mem.Lift.WeylAction.weyl_action <;> assumption)
