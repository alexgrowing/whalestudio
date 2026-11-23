import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductIntegralEqZeroOfMemRelIdeal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grassmannProductIntegral_eq_zero_of_mem_relIdeal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), Q ∈ relIdeal H Dw → intGr H Dw Q = 0 := by
  first | exact @GlobalTheory.GrassTop.intGr_eq_zero_of_mem_relIdeal | exact GlobalTheory.GrassTop.intGr_eq_zero_of_mem_relIdeal | (intros; apply GlobalTheory.GrassTop.intGr_eq_zero_of_mem_relIdeal <;> assumption)
