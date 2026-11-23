import Mathlib

theorem UpperTheory.Reformulated.B.KudlaSiegelWeil.exists_den :
    ∀ {K : Type} [inst : Field K] [NumberField K] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V) {y : V},
    y ∈ Submodule.span K (↑L : Set V) →
      ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • y ∈ L := by
  intro K _ _ V _ _ _ _ L y hy
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers K)) K (↑L : Set V) y hy
  refine ⟨t, nonZeroDivisors.ne_zero t.2, ?_⟩
  rw [Submodule.span_eq] at ht
  exact ht
