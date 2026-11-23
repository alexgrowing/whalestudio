import Mathlib

namespace GlobalTheory.ExistsSmulMem

theorem exists_smul_mem {E : Type} [inst : Field E] [NumberField E] {N : ℕ}
    (Lb : Submodule (NumberField.RingOfIntegers E) (Fin N → E))
    (h : Submodule.span E (↑Lb : Set (Fin N → E)) = ⊤) (v : Fin N → E) :
    ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • v ∈ Lb := by
  have hv : v ∈ Submodule.span E (↑Lb : Set (Fin N → E)) := h ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Lb.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Lb.smul_mem _ hax
    · rw [mul_smul]; exact Lb.smul_mem _ hby
  | smul r x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) r
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (NumberField.RingOfIntegers E) E q ≠ 0 := by
      intro h0
      exact hq0 (FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers E) E
        (by rw [h0, map_zero]))
    refine ⟨q * a, mul_ne_zero hq0 ha, ?_⟩
    have key : (q * a) • ((algebraMap (NumberField.RingOfIntegers E) E p /
        algebraMap (NumberField.RingOfIntegers E) E q) • x) = p • (a • x) := by
      rw [← algebraMap_smul E (q * a), ← algebraMap_smul E p, ← algebraMap_smul E a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact Lb.smul_mem _ hax

end GlobalTheory.ExistsSmulMem
