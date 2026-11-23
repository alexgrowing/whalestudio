import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusAnglesOfUnimodularProdOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsOrth
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusAngles_of_unimodular_prod_one : ∀ (r : ℕ) (z : Fin r → ℂ), (∀ a, ‖z a‖ = 1) → ∏ a, z a = 1 → ∃ φ : Fin (r - 1) → ℝ, ∀ a, Complex.exp (Complex.I * (angles φ a : ℂ)) = z a := by
  first | exact @GlobalTheory.TorusAngles.exists_angles_of_prod_eq_one | exact GlobalTheory.TorusAngles.exists_angles_of_prod_eq_one | (intros; apply GlobalTheory.TorusAngles.exists_angles_of_prod_eq_one <;> assumption)
