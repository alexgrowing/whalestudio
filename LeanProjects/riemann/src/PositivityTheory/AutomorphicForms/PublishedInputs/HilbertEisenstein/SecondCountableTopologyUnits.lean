import GroundTheory.LocalFields.LocalZeta
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
import GroundTheory.LocalFields.LocalFourierHaar

noncomputable section

open MeasureTheory GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.MultiplicativeHaarInverse

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

instance secondCountableTopology_units : SecondCountableTopology Kˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

instance sigmaCompactSpace_units : SigmaCompactSpace Kˣ := inferInstance

instance regular_multHaar : (multHaar K).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

instance isInvInvariant_multHaar : (multHaar K).IsInvInvariant :=
  Measure.IsHaarMeasure.isInvInvariant_of_regular (multHaar K)

theorem inv_subst (f : Kˣ → ℂ) (t : Kˣ) :
    (Integrable f (multHaar K) ↔ Integrable (fun x => f (t * x⁻¹)) (multHaar K)) ∧
    ∫ a, f a ∂multHaar K = ∫ x, f (t * x⁻¹) ∂multHaar K := by
  have h1 : (fun x => f (t * x⁻¹)) = fun x => f (t / x) := by
    funext x
    rw [div_eq_mul_inv]
  rw [h1]
  exact ⟨(integrable_comp_div_left f t).symm, (integral_div_left_eq_self f (multHaar K) t).symm⟩

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.MultiplicativeHaarInverse
