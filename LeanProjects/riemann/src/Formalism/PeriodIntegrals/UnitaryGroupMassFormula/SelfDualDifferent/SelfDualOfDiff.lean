import Mathlib
import Formalism.PeriodIntegrals.SelfDualOfDiff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualDifferent.Imports

noncomputable section
open NumberField

namespace PI.UnitaryGroupMassFormula.KerSelfDual

theorem selfDualOfDiff : PI.KerIso.SelfDualOfDiff := by
  intro K E _ _ _ _ _ cj 𝔟 𝔟c hconj hc hd
  have hD : ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) =
      (FractionalIdeal.dual (𝓞 K) K (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ :=
    coeIdeal_differentIdeal (𝓞 K) K E (𝓞 E)
  have hdual1 : FractionalIdeal.dual (𝓞 K) K (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero (𝓞 K) K one_ne_zero
  have hD0 : differentIdeal (𝓞 K) (𝓞 E) ≠ ⊥ := by
    intro h
    rw [h, FractionalIdeal.coeIdeal_bot] at hD
    exact inv_ne_zero hdual1 hD.symm
  have hb : 𝔟 ≠ ⊥ := by
    rintro rfl
    exact hD0 (by rw [hd, Ideal.bot_mul])
  have hbc : 𝔟c ≠ ⊥ := by
    rintro rfl
    exact hD0 (by rw [hd, Ideal.mul_bot])
  have hb0 : ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hb
  have hbc0 : ((𝔟c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hbc
  have hdual : FractionalIdeal.dual (𝓞 K) K ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ =
      ((𝔟c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ := by
    rw [FractionalIdeal.dual_inv, ← inv_inv (FractionalIdeal.dual (𝓞 K) K 1), ← hD, hd,
      FractionalIdeal.coeIdeal_mul, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
  intro y
  rw [inv_map cj hconj.1 𝔟 𝔟c hc hb hbc y, ← hdual,
    FractionalIdeal.mem_dual (inv_ne_zero hb0)]
  refine forall₂_congr fun x _ => ?_
  rw [Algebra.traceForm_apply, mul_comm]

end PI.UnitaryGroupMassFormula.KerSelfDual
