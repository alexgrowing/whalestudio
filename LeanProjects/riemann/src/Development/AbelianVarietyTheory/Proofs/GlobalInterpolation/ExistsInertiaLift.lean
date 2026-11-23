import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.TorIsoId
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationIntegerLeOne
open NumberField IsDedekindDomain Polynomial GlobalTheory.CMRam GlobalTheory.FieldSize
open scoped nonZeroDivisors

namespace GlobalTheory.CMRam

theorem val_int_le {E Ω : Type*} [Field E] [Field Ω] (ι : E →+* Ω) (A : ValuationSubring Ω) (a : 𝓞 E) :
    A.valuation (ι a) ≤ 1 :=
  (A.valuation_le_one_iff _).2
    (ReciprocityTheory.Gal.mem_of_isIntegral_int A (a.isIntegral_coe.map ι.toIntAlgHom))

theorem exists_den_field {E Ω : Type*} [Field E] [NumberField E] [Field Ω] (ι : E →+* Ω)
    (A : ValuationSubring Ω) {x : E} (hx : A.valuation (ι x) ≤ 1) :
    ∃ s t : 𝓞 E, A.valuation (ι s) = 1 ∧ (s : E) * x = t := by
  first
  | exact @_root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator
  | exact _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator
  | (apply _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator ..)

end GlobalTheory.CMRam
