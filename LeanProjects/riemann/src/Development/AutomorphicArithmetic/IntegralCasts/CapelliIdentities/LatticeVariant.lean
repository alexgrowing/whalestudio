import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost

theorem UpperTheory.Reformulated.B.LatticeVariant.lsd_spanDen :
    ∀ {D : Formalism.BasicNotions.D7} {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E)),
    Submodule.span D.host.E (↑L : Set (Fin n → D.host.E)) = ⊤ →
      ∀ (x : Fin n → D.host.E),
        ∃ (d : NumberField.RingOfIntegers D.host.E),
          d ≠ (0 : NumberField.RingOfIntegers D.host.E) ∧
            (↑d : D.host.E) • x ∈
              L := by
  intro D n L hL x
  have hx : x ∈ Submodule.span D.host.E (↑L : Set (Fin n → D.host.E)) := hL ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.host.E)) D.host.E _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, nonZeroDivisors.ne_zero t.2, ht⟩
