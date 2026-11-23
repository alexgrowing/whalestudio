import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost

theorem UpperTheory.Reformulated.B.Qf52.not_both :
    ∀ (D : Formalism.BasicNotions.D7) (p : Formalism.MainNotions.S.LocalSplitGroups.PlF D),
    (↑(D.host.g (0 : Fin (2 : ℕ))) : NumberField.RingOfIntegers ↥D.host.F) ∈ p.asIdeal →
      (↑(D.host.g (1 : Fin (2 : ℕ))) : NumberField.RingOfIntegers ↥D.host.F) ∈ p.asIdeal →
        False := by
  intro D p h0 h1
  have hc : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
    (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
  obtain ⟨a, b, hab⟩ : IsCoprime
      (D.host.g 0 : NumberField.RingOfIntegers ↥D.host.F) (D.host.g 1) := hc.cast
  apply p.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact p.asIdeal.add_mem (p.asIdeal.mul_mem_left a h0) (p.asIdeal.mul_mem_left b h1)
