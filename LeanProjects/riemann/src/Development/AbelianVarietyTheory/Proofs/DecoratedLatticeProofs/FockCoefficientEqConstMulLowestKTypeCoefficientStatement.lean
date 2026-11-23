import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientEqConstMulLowestKTypeCoefficient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockCoefficient_eq_const_mul_lowestKTypeCoefficient : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), GlobalTheory.HolDict.HolShape M → (∃ wt, GlobalTheory.HolDict.WtIs M wt) → ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 → ∀ c : CoefA S, c.Is → ∀ pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ), (∀ P, IsThetaFunO ψ S T (pt P)) → ∀ (Δ : PolF D T.rank S.rank) (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank), IsIoW θ M c om (fun P => pt P) Δ io → GlobalTheory.RawLift.FockCoef.Killed om θ M (pt Δ) → ∀ w : c.W, ∃ N : ℂ, ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ (e e' : ∀ ρ, lowT M ρ), l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) w))) (pt (io (PiTensorProduct.tprod ℂ e') w)) = N * (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) := by
  first | exact @GlobalTheory.RawLift.FockPair.coef_one_vector | exact GlobalTheory.RawLift.FockPair.coef_one_vector | (intros; apply GlobalTheory.RawLift.FockPair.coef_one_vector <;> assumption)
