import Mathlib

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Bl.general_b_fact_right_ter

theorem goal1 {F : Type} [Field F] [NumberField F] {ι : Type} (s : Finset ι)
    (Q : ι → 𝓞 F → Prop) (hQ : ∀ i c r, Q i c → Q i (c * r)) (h : ∀ i ∈ s, ∃ c, c ≠ 0 ∧ Q i c) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i ∈ s, Q i c := by
  classical
  choose! c hc0 hcQ using h
  refine ⟨∏ i ∈ s, c i, Finset.prod_ne_zero_iff.mpr hc0, ?_⟩
  intro i hi
  rw [← Finset.mul_prod_erase s c hi]
  exact hQ i _ _ (hcQ i hi)

end Bl.general_b_fact_right_ter
