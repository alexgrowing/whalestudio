import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LpCoefficientCenterNormPreserved
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lp_coefficient_center_norm_preserved : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (p : ℝ), CoeffLp p π → ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ (v : V) (l : Module.Dual ℂ V), IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} → ‖l (π z v)‖ = ‖l v‖ := by
  first | exact @GlobalTheory.CompanionTheory.CoeffCentral.norm_coeff_central | exact GlobalTheory.CompanionTheory.CoeffCentral.norm_coeff_central | (intros; apply GlobalTheory.CompanionTheory.CoeffCentral.norm_coeff_central <;> assumption)
