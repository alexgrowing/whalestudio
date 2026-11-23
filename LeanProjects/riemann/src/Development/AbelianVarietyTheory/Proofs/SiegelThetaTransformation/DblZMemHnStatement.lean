import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dblZ_mem_Hn_and_det_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, IsType X.Ψ ∧ dblZ X x₁ x₂ ∈ Hn X.Ψ r ∧ ∀ τ, (aLin X x₁ x₂ τ).det ≠ 0 ∧ (aAnti X x₁ x₂ τ).det ≠ 0 ∧ aLin X x₂ x₁ τ = (aAnti X x₁ x₂ τ).map conj := by
  first | exact @GlobalTheory.SW.dblZ_mem_Hn | exact GlobalTheory.SW.dblZ_mem_Hn | (intros; apply GlobalTheory.SW.dblZ_mem_Hn <;> assumption)
