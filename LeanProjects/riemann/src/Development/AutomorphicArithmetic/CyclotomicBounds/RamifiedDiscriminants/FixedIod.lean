import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.PrimeDiscriminants.CycImage

open NumberField Formalism.BasicNotions

namespace UpperTheory.Ram

theorem image_mem_of_fixed_iod {R : Ranks} (H : Host R) {Ω : Type} [Field Ω] [IsAlgClosed Ω] (J : H.E →+* Ω) (M : Subfield Ω)
    (hM : ∀ y : Ω, y ^ (H.QS * H.q) = 1 → y ∈ M) (x : H.E) (hx : H.sigmaOf R.toFrame.iod x = x) : J x ∈ M := by
  refine H.toHostRaw.image_mem_of_fixed J M (Dvd.intro _ rfl) hM x fun u hu => ?_
  rcases H.art_d u hu with h | h
  · rw [h, map_one]; rfl
  · rw [h]; exact hx

end UpperTheory.Ram
