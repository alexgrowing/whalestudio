import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.DifferentIdealMapNeBot

set_option linter.unusedVariables false

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def intS : Subring D.host.E := (integralClosure ℤ D.host.E).toSubring

theorem coe_mem_intS (c : 𝓞 D.host.E) : (c : D.host.E) ∈ intS D := c.isIntegral_coe

def IntM {N : ℕ} (Z : Matrix (Fin N) (Fin N) D.host.E) : Prop := ∀ a b, Z a b ∈ intS D

theorem max_inv_eq {x : ℝ} (hx : 0 < x) : max 1 x⁻¹ = max 1 x / x := by
  rcases le_total 1 x with h | h
  · rw [max_eq_left (inv_le_one_of_one_le₀ h), max_eq_right h, div_self hx.ne']
  · rw [max_eq_right (one_le_inv₀ hx |>.2 h), max_eq_left h, one_div]

theorem prod_max_inv_le {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, 0 < x i) (h1 : 1 ≤ ∏ i, x i) :
    ∏ i, max 1 (x i)⁻¹ ≤ ∏ i, max 1 (x i) := by
  have hP : 0 < ∏ i, x i := Finset.prod_pos fun i _ => hx i
  have hM : 0 ≤ ∏ i, max 1 (x i) := Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_left _ _)
  calc ∏ i, max 1 (x i)⁻¹ = ∏ i, (max 1 (x i) / x i) := Finset.prod_congr rfl fun i _ => max_inv_eq (hx i)
    _ = (∏ i, max 1 (x i)) / ∏ i, x i := Finset.prod_div_distrib _ _
    _ ≤ ∏ i, max 1 (x i) := div_le_self hM h1

end Formalism.MainNotions.S.Pv.HH

end
