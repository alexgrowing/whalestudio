import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

namespace GlobalTheory.ChartDomain

open NumberField in

theorem _root_.GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x →
    ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom := by
  intro E _ _ _ r X x z hx hz
  have hsmall : (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 := by
    by_cases hr : (r : ℝ) = 0
    · simp [hr]
    · have hpos : 0 < (r : ℝ) ^ 2 := by positivity
      calc (r : ℝ) ^ 2 * ‖z‖ ≤ (r : ℝ) ^ 2 * (1 / (100 * (r : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hz hpos.le
        _ = 1 / 100 := by field_simp
  exact (_root_.GlobalTheory.dmin_rmul_near_one X x hx (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) (norm_nonneg z) hsmall
    (fun τ a b => _root_.GlobalTheory.ChartNearOne.nmat_entry_le X z τ a b)).1

end GlobalTheory.ChartDomain
