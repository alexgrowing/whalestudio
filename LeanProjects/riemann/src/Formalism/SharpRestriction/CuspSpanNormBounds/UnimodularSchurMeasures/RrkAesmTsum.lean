import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {G : Type*} [Group G]

def rrk_K (Γ : Subgroup G) (φ : G → ℂ) (x y : G) : ℂ := ∑' γ : Γ, φ (x⁻¹ * (γ : G) * y)

def rrk_Kab (Γ : Subgroup G) (φ : G → ℂ) (x y : G) : ℝ≥0∞ := ∑' γ : Γ, ‖φ (x⁻¹ * (γ : G) * y)‖ₑ

theorem rrk_aesm_tsum {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι] {f : ι → α → ℂ}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hs : ∀ᵐ x ∂μ, Summable fun i => f i x) :
    AEStronglyMeasurable (fun x => ∑' i, f i x) μ := by
  refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ι))
    (f := fun s x => ∑ i ∈ s, f i x) (fun s => ?_) ?_
  · exact Finset.aestronglyMeasurable_fun_sum s fun i _ => hf i
  · filter_upwards [hs] with x hx
    exact hx.hasSum

end Formalism.MainNotions.LeviCoordinates

end
