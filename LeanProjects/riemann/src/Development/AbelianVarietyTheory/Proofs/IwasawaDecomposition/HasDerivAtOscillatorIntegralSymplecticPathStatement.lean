import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtOscillatorIntegralSymplecticPath
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSet
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_oscillatorIntegral_symplecticPath : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ (a : ℝ → V →L[ℝ] V) (X : V →L[ℝ] V), a 0 = 1 → HasDerivAt a X 0 → (∀ t x y, omJ J (a t x) (a t y) = omJ J x y) → ∀ (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → V), IsQuadOf (omJ J) X c p q → ∃ lam : ℂ, ∀ f, Sm ρ f → HasDerivAt (fun t : ℝ => ∫ w, ρ (a t w) (∫ u, gau u • ρ (a t u) (proj h (ρ (-w) f)))) (quad ρ c p q f + lam • f) 0 := by
  first | exact @GlobalTheory.Mem.Lift.OscDeriv.hasDerivAt_osc | exact GlobalTheory.Mem.Lift.OscDeriv.hasDerivAt_osc | (intros; apply GlobalTheory.Mem.Lift.OscDeriv.hasDerivAt_osc <;> assumption)
