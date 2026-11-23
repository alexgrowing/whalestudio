import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataRows
import Formalism.LocalRingCardinality.DataArith
import Formalism.LocalRingCardinality.DataForms

theorem UpperTheory.Reformulated.B.ExistsIdealDenominator.exists_denI :
    ∀ {D : Formalism.BasicNotions.D7} (u : D.what₂.Word) (i : ℕ) (x : ((D.fm u).lat i).V),
    ∃ (d : NumberField.RingOfIntegers D.what₂.LL),
      d ≠ (0 : NumberField.RingOfIntegers D.what₂.LL) ∧
        d • x ∈
          ((D.fm u).lat
              i).L := by
  intro D u i x
  have hx : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat i).L : Set ((D.fm u).lat i).V) := by
    rw [((D.fm u).lat_good i).2.2]
    exact Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.what₂.LL)) D.what₂.LL _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, nonZeroDivisors.ne_zero t.2, ht⟩
