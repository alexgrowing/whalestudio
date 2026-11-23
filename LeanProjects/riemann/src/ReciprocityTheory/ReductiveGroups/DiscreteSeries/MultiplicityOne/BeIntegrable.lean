import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.TranslateIntegrable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepro

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace Topology

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem l_eq (D : RealPlaceData k r Wp Wp) (X : SigData k r) {l : X.Hs → Wp} (hl : IsMultOneMap D X l) {v₀ : X.Hs}
    (hv₀ : v₀ ∈ Vfl X) (hne : l v₀ ≠ 0) {u : X.Hs} (hu : u ∈ Vfl X) :
    l u = (⟪l v₀, l v₀⟫_ℂ)⁻¹ • beOp D X u v₀ (l v₀) := by
  have h0 : ⟪l v₀, l v₀⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hne
  rw [hl.2 u hu v₀ hv₀]
  simp only [rk1, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
  rw [inv_mul_cancel₀ h0, one_smul]

end ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit
