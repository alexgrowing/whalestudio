import Mathlib

noncomputable def UpperTheory.Reformulated.B.PadicComplexIntegerSubring.intSub :
    (p : ℕ) → [inst : Fact (Nat.Prime p)] → Subring ℂ_[p] := fun p _ =>
  { carrier := {x : ℂ_[p] | ‖x‖ ≤ 1}
    mul_mem' := fun {a b} ha hb => by
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      rw [norm_mul]
      exact mul_le_one₀ ha (norm_nonneg b) hb
    one_mem' := by
      simp only [Set.mem_setOf_eq, norm_one, le_refl]
    add_mem' := fun {a b} ha hb => by
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
    zero_mem' := by
      simp only [Set.mem_setOf_eq, norm_zero, zero_le_one]
    neg_mem' := fun {a} ha => by
      simp only [Set.mem_setOf_eq] at ha ⊢
      rwa [norm_neg] }
