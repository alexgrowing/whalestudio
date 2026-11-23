import Mathlib

theorem UpperTheory.Reformulated.B.Qk22.prod_mem_pow :
    ∀ {R k : Type} [inst : CommRing R] [inst_1 : CommRing k]
    [inst_2 : Algebra R k] (J : Submodule R k) {β : Type} (t : Finset β) (x : β → k) (e : β → ℕ),
    (∀ b ∈ t, x b ∈ J ^ e b) → ∏ b ∈ t, x b ∈ J ^ ∑ b ∈ t, e b := by
  intro R k _ _ _ J β t x e h
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, pow_zero]
    exact Submodule.one_le.mp le_rfl
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, pow_add]
    exact Submodule.mul_mem_mul (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
