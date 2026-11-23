import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Imports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthEqTopOfFinrankNeZero

namespace GlobalTheory

open IsDiscreteValuationRing

section CokernelLength

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem length_quot_range_eq_addVal_det {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  first
  | exact @_root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det
  | exact _root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det
  | (apply _root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det ..)

end CokernelLength

end GlobalTheory
