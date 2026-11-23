import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost

theorem UpperTheory.Reformulated.B.Qf38.mem_inv_coe :
    ∀ (D : Formalism.BasicNotions.D7) {J : Ideal (NumberField.RingOfIntegers D.host.E)},
    J ≠ ⊥ →
      ∀ (x : D.host.E),
        x ∈ (↑J : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers D.host.E)) D.host.E)⁻¹ ↔
          ∀ y ∈ J,
            ∃ (o : NumberField.RingOfIntegers D.host.E),
              (↑o : D.host.E) =
                x *
                  (↑y :
                    D.host.E) := by
  intro D J hJ x
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr hJ)]
  constructor
  · intro h y hy
    exact (FractionalIdeal.mem_one_iff _).mp
      (h _ ((FractionalIdeal.mem_coeIdeal _).mpr ⟨y, hy, rfl⟩))
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hz
    exact (FractionalIdeal.mem_one_iff _).mpr (h y hy)
