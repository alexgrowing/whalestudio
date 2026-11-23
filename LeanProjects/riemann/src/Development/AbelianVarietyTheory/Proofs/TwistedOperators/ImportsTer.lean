import Mathlib

namespace GlobalTheory.TargetStatementSixOneSixtyEight

open NumberField

theorem main {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (L : Submodule (RingOfIntegers E) V) {y : V} (hy : y ∈ Submodule.span E (L : Set V)) :
    ∃ c : RingOfIntegers E, c ≠ 0 ∧ c • y ∈ L := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ h1 h2 =>
    obtain ⟨c1, hc1, h1⟩ := h1
    obtain ⟨c2, hc2, h2⟩ := h2
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
    rw [smul_add, mul_comm c1 c2, mul_smul, mul_comm c2 c1, mul_smul]
    exact L.add_mem (L.smul_mem c2 h1) (L.smul_mem c1 h2)
  | smul a x _ h =>
    obtain ⟨c0, hc0, h0⟩ := h
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a
    refine ⟨c0 * (s : RingOfIntegers E), mul_ne_zero hc0 (nonZeroDivisors.coe_ne_zero s), ?_⟩
    have key : (s : RingOfIntegers E) • (a • x) = b • x := by
      rw [← algebraMap_smul E (s : RingOfIntegers E), smul_smul, mul_comm, hs, algebraMap_smul]
    rw [mul_smul, key, smul_comm c0 b x]
    exact L.smul_mem b h0

theorem target : ∀ {E : Type} [inst : Field E] [NumberField E] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : Module E V] [inst_4 : Module (NumberField.RingOfIntegers E) V]
    [IsScalarTower (NumberField.RingOfIntegers E) E V]
    (L : Submodule (NumberField.RingOfIntegers E) V) {y : V},
    y ∈ Submodule.span E (↑L : Set V) →
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • y ∈ L :=
  fun L _ hy => main L hy

end GlobalTheory.TargetStatementSixOneSixtyEight
