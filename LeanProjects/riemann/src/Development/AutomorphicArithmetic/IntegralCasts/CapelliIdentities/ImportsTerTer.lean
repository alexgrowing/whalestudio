import Mathlib

noncomputable def UpperTheory.Reformulated.B.PadicComplexValuationRing.intS (p : ℕ) [inst : Fact (Nat.Prime p)] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := fun {a b} ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  mul_mem' := fun {a b} ha hb =>
    (norm_mul_le a b).trans (mul_le_one₀ ha (norm_nonneg b) hb)
  neg_mem' := fun {a} ha => by
    simpa only [Set.mem_setOf_eq, norm_neg] using ha
