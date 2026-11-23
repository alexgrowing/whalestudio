import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

noncomputable section

open NumberField MeasureTheory
open GlobalTheory.CuspRep (Cinf Lie)

namespace UpperTheory.V.TG

variable (E : Type) [Field E] [NumberField E]

instance : (volume : Measure (Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

instance (a : ℕ) : (volume : Measure (Fin a → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

instance (a : ℕ) : (volume : Measure (Lie E a)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

def tr : Cinf E →ₗ[ℝ] ℝ where
  toFun x := ∑ w, 2 * (x w).re
  map_add' x y := by simp only [Pi.add_apply, Complex.add_re, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, Complex.real_smul, Complex.re_ofReal_mul, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem tr_apply (x : Cinf E) : tr E x = ∑ w, 2 * (x w).re := rfl

end UpperTheory.V.TG
