import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepThetaFunctionPolynomialGrowthRealPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_thetaFunction_polynomialGrowth_realPoints : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → ∀ θ : InfF D, IsInfFam θ → ∃ N : ℕ, ∀ f, IsThetaFunO ψ S T f → ∀ x y, ∃ C : ℝ, ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ w, ‖om (x * a, y * b) f w‖ ≤ C * ((1 + normInf θ S a) * (1 + normInf θ T b)) ^ N := by
  first | exact @GlobalTheory.Mem.LiftBound.om_growth | exact GlobalTheory.Mem.LiftBound.om_growth | (intros; apply GlobalTheory.Mem.LiftBound.om_growth <;> assumption)
