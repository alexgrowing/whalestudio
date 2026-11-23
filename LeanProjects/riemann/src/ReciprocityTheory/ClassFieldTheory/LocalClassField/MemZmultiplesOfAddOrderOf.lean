import Mathlib
import ReciprocityTheory.NeutralLocalFields.Duality

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 Function

namespace RationalModIntegerChains

open scoped Nat

variable {A : Type} [AddCommGroup A]

section Chain

variable {C : Type} [AddCommGroup C]

theorem chain_shift (c : ℕ → C) (hc : ∀ n, (n + 1) • c (n + 1) = c n) (n d : ℕ) :
    ∃ e : ℕ, c n = e • c (n + d) := by
  induction d with
  | zero => exact ⟨1, by simp⟩
  | succ d ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e * (n + d + 1), ?_⟩
    rw [mul_nsmul', ← add_assoc, hc, ← he]

def chainSub (c : ℕ → C) (hc : ∀ n, (n + 1) • c (n + 1) = c n) : AddSubgroup C where
  carrier := {x | ∃ (n : ℕ) (k : ℤ), x = k • c n}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨n, k, rfl⟩ ⟨m, l, rfl⟩
    obtain ⟨e, he⟩ := chain_shift c hc n m
    obtain ⟨f, hf⟩ := chain_shift c hc m n
    refine ⟨n + m, k * e + l * f, ?_⟩
    rw [add_comm m n] at hf
    rw [add_zsmul, mul_zsmul, mul_zsmul, natCast_zsmul, natCast_zsmul, ← he, ← hf]
  neg_mem' := by
    rintro _ ⟨n, k, rfl⟩
    exact ⟨n, -k, by simp⟩

end Chain

noncomputable def qzc (n : ℕ) : QZ := QuotientAddGroup.mk (1 / (n ! : ℚ))

theorem qz_torsion (x : QZ) : ∃ k : ℕ, 0 < k ∧ k • x = 0 := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨q.den, q.den_pos, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  exact ⟨q.num, by
    show (q.num : ℚ) = _
    rw [nsmul_eq_mul, mul_comm, Rat.mul_den_eq_num]⟩

end RationalModIntegerChains

end ReciprocityTheory.DiscreteGroups.LocalClassField
