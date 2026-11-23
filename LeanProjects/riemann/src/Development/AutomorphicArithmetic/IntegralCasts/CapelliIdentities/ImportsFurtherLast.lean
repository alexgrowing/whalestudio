import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost

theorem UpperTheory.Reformulated.B.Rd4.exists_nat_smul_mem :
    ∀ {D : Formalism.BasicNotions.D7} {n : ℕ}
    {Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E)},
    Submodule.IsLattice D.host.E Λ →
      ∀ (x : Fin n → D.host.E),
        ∃ (N : ℕ),
          (0 : ℕ) < N ∧
            (↑N : D.host.E) • x ∈
              Λ := by
  intro D n Λ h x
  obtain ⟨⟨_, m, hm, rfl⟩, ht⟩ := multiple_mem_span_of_mem_localization_span
    (Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers D.host.E) (nonZeroDivisors ℤ))
    D.host.E (Λ : Set (Fin n → D.host.E)) x (by rw [h.span_eq_top]; trivial)
  change algebraMap ℤ (NumberField.RingOfIntegers D.host.E) m • x ∈ _ at ht
  rw [Submodule.span_eq, algebraMap_smul] at ht
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  refine ⟨m.natAbs * m.natAbs, by positivity, ?_⟩
  rw [Nat.cast_smul_eq_nsmul, ← natCast_zsmul, Int.natAbs_mul_self, mul_smul]
  exact zsmul_mem ht m
