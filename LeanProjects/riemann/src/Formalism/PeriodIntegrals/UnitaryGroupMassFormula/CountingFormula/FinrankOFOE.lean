import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowers

open NumberField Module Formalism.MainNotions.S

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_OF_OE (D : Formalism.BasicNotions.D7) : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 := by
  rw [← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E]
  have h1 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  rw [D.host.der.finrank_E, D.host.der.finrank_F] at h1
  have hpos : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
  rw [D.host.der.finrank_E] at hpos

  have key : ∀ o x : ℕ, 2 * o * x = 4 * o → 0 < 4 * o → x = 2 := by
    intro o x h hp
    have ho : 0 < 2 * o := by omega
    exact Nat.eq_of_mul_eq_mul_left ho (by rw [h]; ring)
  exact key _ _ h1 hpos

theorem absNorm_ddS (D : Formalism.BasicNotions.D7) :
    FractionalIdeal.absNorm (ddS D) = (((NumberField.discr D.host.F).natAbs : ℚ)) ^ 2 := by
  have h := FractionalIdeal.absNorm_eq' (K := D.host.E) (I := ddS D) 1
    (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)))
    (by
      first
        | (open scoped Pointwise in rw [one_smul]; rfl)
        | (exact (one_smul _ _).trans rfl)
        | (open scoped Pointwise in simp; rfl))
  rw [h, Ideal.absNorm_algebraMap, finrank_OF_OE,
    NumberField.absNorm_differentIdeal (K := D.host.F)]
  simp

end PI.UnitaryGroupMassFormula.CntFormula.R6
