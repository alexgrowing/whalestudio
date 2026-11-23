import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCmTypeProductSq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_cm_type_product_sq : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → ∀ d : E, ‖∏ τ : Ψ, τ.1 d‖ ^ 2 = |((Algebra.norm ℚ d : ℚ) : ℝ)| := by
  first | exact @GlobalTheory.cm_type_normSq_prod_eq_abs_norm | exact GlobalTheory.cm_type_normSq_prod_eq_abs_norm | (intros; apply GlobalTheory.cm_type_normSq_prod_eq_abs_norm <;> assumption)
