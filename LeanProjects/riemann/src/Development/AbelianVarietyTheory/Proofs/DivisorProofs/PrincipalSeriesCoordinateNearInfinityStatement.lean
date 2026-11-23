import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesCoordinateNearInfinity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_series_coordinate_near_infinity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ, ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) → GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1 := by
  first | exact @GlobalTheory.PrinTwo.coord_eq_of_far | exact GlobalTheory.PrinTwo.coord_eq_of_far | (intros; apply GlobalTheory.PrinTwo.coord_eq_of_far <;> assumption)
