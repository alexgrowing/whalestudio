import Mathlib

theorem UpperTheory.Reformulated.B.SpanDenominator.den_of_span :
    ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] {i : ℕ} (P : Ideal (NumberField.RingOfIntegers K))
      [inst_2 : P.IsPrime] (M : Submodule (NumberField.RingOfIntegers K) (Fin i → K)),
      ∀
        x ∈
          Submodule.span ↥(Localization.subalgebra.ofField K P.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P))
            (↑M : Set (Fin i → K)),
        ∃ s ∈ P.primeCompl, s • x ∈ M := by
  intro K _ _ i P _ M x hx
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span P.primeCompl
    ↥(Localization.subalgebra.ofField K P.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P))
    (↑M : Set (Fin i → K)) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, t.2, ht⟩
