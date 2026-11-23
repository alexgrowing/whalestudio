import Mathlib

namespace GlobalTheory.FiniteIndexSubgroup

open NumberField

private theorem exists_ne_zero_smul_mem_of_mem_span' {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) :
    ∀ x ∈ Submodule.span E (L : Set (Fin n → E)), ∃ ν : RingOfIntegers E, ν ≠ 0 ∧ ν • x ∈ L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • z = a • (b • z) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact L.add_mem (L.smul_mem b hax) (L.smul_mem a hbz)
  | smul c x _ hx =>
    obtain ⟨ν, hν, hνx⟩ := hx
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hb' : algebraMap (RingOfIntegers E) E b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hsc : algebraMap (RingOfIntegers E) E (b * ν) * c = algebraMap (RingOfIntegers E) E (a * ν) := by
      rw [← hab, map_mul, map_mul]
      field_simp
    refine ⟨b * ν, mul_ne_zero hb0 hν, ?_⟩
    have : (b * ν) • (c • x) = a • (ν • x) := by
      calc (b * ν) • (c • x) = (algebraMap (RingOfIntegers E) E (b * ν)) • (c • x) :=
            (algebraMap_smul E _ _).symm
        _ = (algebraMap (RingOfIntegers E) E (b * ν) * c) • x := smul_smul _ _ _
        _ = (algebraMap (RingOfIntegers E) E (a * ν)) • x := by rw [hsc]
        _ = (a * ν) • x := algebraMap_smul E _ _
        _ = a • (ν • x) := mul_smul _ _ _
    rw [this]
    exact L.smul_mem a hνx

theorem main {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ ν : RingOfIntegers E, ν ≠ 0 ∧ ν • y ∈ L := exists_ne_zero_smul_mem_of_mem_span' L y (by rw [hL]; exact Submodule.mem_top)

theorem target : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.span E (↑L : Set (Fin n → E)) = ⊤ → ∀ (y : Fin n → E), ∃ (ν : NumberField.RingOfIntegers E), ν ≠ (0 : NumberField.RingOfIntegers E) ∧ ν • y ∈ L := by
  intro E _ _ n L hL y
  exact exists_ne_zero_smul_mem_of_mem_span' L y (by rw [hL]; exact Submodule.mem_top)

end GlobalTheory.FiniteIndexSubgroup
