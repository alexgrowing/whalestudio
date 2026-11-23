import Mathlib

namespace GlobalTheory.NatSmulMem

theorem exists_nat_smul_mem {R : Type} [inst : CommRing R] {O : Subring R} {n : ℕ}
    (Λ : Submodule (↥O) (Fin n → R))
    (h : ∀ (y : R), ∃ (m : ℕ), m ≠ (0 : ℕ) ∧ (↑m : R) * y ∈ O) {x : Fin n → R}
    (hx : x ∈ Submodule.span R (↑Λ : Set (Fin n → R))) :
    ∃ (m : ℕ), m ≠ (0 : ℕ) ∧ (↑m : R) • x ∈ Λ := by
  have key : ∀ (c : R), c ∈ O → ∀ v : Fin n → R, v ∈ Λ → c • v ∈ Λ :=
    fun c hc v hv => Λ.smul_mem (⟨c, hc⟩ : O) hv
  induction hx using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_ne_zero, by simpa using hv⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha, hau⟩ := hu
    obtain ⟨b, hb, hbv⟩ := hv
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : ((a * b : ℕ) : R) • (u + v) = (b : R) • ((a : R) • u) + (a : R) • ((b : R) • v) := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (b : R) (a : R)]
    rw [e]
    exact Λ.add_mem (key _ (natCast_mem O b) _ hau) (key _ (natCast_mem O a) _ hbv)
  | smul r v _ hv =>
    obtain ⟨a, ha, hav⟩ := hv
    obtain ⟨b, hb, hbr⟩ := h r
    refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
    have e : ((b * a : ℕ) : R) • (r • v) = ((b : R) * r) • ((a : R) • v) := by
      rw [smul_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
    rw [e]
    exact key _ hbr _ hav

end GlobalTheory.NatSmulMem
