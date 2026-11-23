import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesZeroOfCoordinateZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_series_zero_of_coordinate_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), GlobalTheory.PrinTwo.ev f 1 = 0 → (∀ x : k, GlobalTheory.PrinTwo.coord f x = 0) → f = 0 := by
  first | exact @GlobalTheory.PrinTwo.eq_zero_of_ev_one_of_coord | exact GlobalTheory.PrinTwo.eq_zero_of_ev_one_of_coord | (intros; apply GlobalTheory.PrinTwo.eq_zero_of_ev_one_of_coord <;> assumption)
