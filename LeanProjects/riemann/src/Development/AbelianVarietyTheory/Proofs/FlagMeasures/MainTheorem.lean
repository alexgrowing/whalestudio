import Mathlib

namespace GlobalTheory.DenominatorTheorem

open NumberField

theorem main_theorem : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (G : Submodule (NumberField.RingOfIntegers E) (Fin n → E)),
    Submodule.span E (↑G : Set (Fin n → E)) = ⊤ → ∀ (y : Fin n → E),
    ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • y ∈ G := by
  intro E _ _ n G hG y
  have hy : y ∈ Submodule.span E (G : Set (Fin n → E)) := hG ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simpa using G.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdz⟩ := hz
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add]
    refine G.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact G.smul_mem d hcx
    · rw [mul_smul]; exact G.smul_mem c hdz
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a
    simp only at hpq
    refine ⟨(q : RingOfIntegers E) * c, mul_ne_zero (nonZeroDivisors.ne_zero q.2) hc, ?_⟩
    have key : ((q : RingOfIntegers E) * c) • (a • x) = p • (c • x) := by
      rw [← algebraMap_smul E ((q : RingOfIntegers E) * c) (a • x), smul_smul,
        ← algebraMap_smul E p (c • x), ← algebraMap_smul E c x, smul_smul, map_mul,
        mul_comm (algebraMap _ E (q : RingOfIntegers E)), mul_assoc, mul_comm _ a, hpq, mul_comm]
    rw [key]
    exact G.smul_mem p hcx

end GlobalTheory.DenominatorTheorem
