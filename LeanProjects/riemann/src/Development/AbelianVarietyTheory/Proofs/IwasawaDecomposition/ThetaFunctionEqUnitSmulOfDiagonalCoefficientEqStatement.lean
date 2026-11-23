import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionEqUnitSmulOfDiagonalCoefficientEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_eq_unitSmul_of_diagonalCoefficient_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f f' : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ w, ∫ x in 𝓕, heisO ψ S T w f' x * star (f' x) ∂μ = ∫ x in 𝓕, heisO ψ S T w f x * star (f x) ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ f' = c • f := by
  first | exact @GlobalTheory.ThetaCoefficient.exists_unit_smul_of_coefficient_eq | exact GlobalTheory.ThetaCoefficient.exists_unit_smul_of_coefficient_eq | (intros; apply GlobalTheory.ThetaCoefficient.exists_unit_smul_of_coefficient_eq <;> assumption)
