import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumProjectorRangeAnnihilated
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FderivCompress
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumProjector_range_annihilated : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ (h : IsHeis (omJ J) ρ) (x : B) (z : V), dH ρ z (proj h x) + I • dH ρ (J z) (proj h x) = 0 := by
  first | exact @GlobalTheory.Mem.Lift.VacAnn.proj_annihilated | exact GlobalTheory.Mem.Lift.VacAnn.proj_annihilated | (intros; apply GlobalTheory.Mem.Lift.VacAnn.proj_annihilated <;> assumption)
