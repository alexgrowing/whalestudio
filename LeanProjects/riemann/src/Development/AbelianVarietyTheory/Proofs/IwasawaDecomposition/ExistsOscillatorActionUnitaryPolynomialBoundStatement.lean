import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOscillatorActionUnitaryPolynomialBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSet
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_oscillatorAction_unitaryPath_quadratic : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ (G : Type) [Group G] (m : G →* Matrix ι ι ℂ), (∀ g, (m g)ᴴ * H * m g = H) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => m g *ᵥ v) Ω ∧ (∃ N : ℕ, ∀ f, Sm ρ f → ∃ C : ℝ, ∀ g, ‖Ω g f‖ ≤ C * (1 + ∑ i, ∑ j, ‖m g i j‖) ^ N) ∧ ∀ (γ : ℝ → G) (X : Matrix ι ι ℂ), γ 0 = 1 → (∀ i j, HasDerivAt (fun t => m (γ t) i j) (X i j) 0) → ∀ (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → ι → ℂ), IsQuadOf (fun x y => (star y ⬝ᵥ H *ᵥ x).im) (fun v => X *ᵥ v) c p q → ∃ lam : ℂ, ∀ f, Sm ρ f → HasDerivAt (fun t => Ω (γ t) f) (quad ρ c p q f + lam • f) 0 := by
  first | exact @GlobalTheory.Mem.Lift.OscBound.exists_osc_bound_deriv | exact GlobalTheory.Mem.Lift.OscBound.exists_osc_bound_deriv | (intros; apply GlobalTheory.Mem.Lift.OscBound.exists_osc_bound_deriv <;> assumption)
