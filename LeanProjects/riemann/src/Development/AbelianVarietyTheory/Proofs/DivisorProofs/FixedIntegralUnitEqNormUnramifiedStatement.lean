import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedIntegralUnitEqNormUnramified
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_integral_unit_eq_norm_unramified : ∀ (K : GlobalTheory.UnitLemma.UQ) (t : K.O), IsUnit t → K.c (algebraMap K.O K.E t) = algebraMap K.O K.E t →
    ∃ v : K.E, v * K.c v = algebraMap K.O K.E t := by
  first | exact @GlobalTheory.UnitLemma.UQ.unit_fixed_is_norm | exact GlobalTheory.UnitLemma.UQ.unit_fixed_is_norm | (intros; apply GlobalTheory.UnitLemma.UQ.unit_fixed_is_norm <;> assumption)
