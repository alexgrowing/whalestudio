import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHartogsPropertyHeightOnePrimesOfFlat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStalkIdealOfCodimOne
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasHartogsPropertyHeightOnePrimes_of_flat : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (B : Type) [CommRing B] [Algebra A B] [Module.Flat A B], GlobalTheory.GoodEtale.Hart A B B := by
  first | (exact @GlobalTheory.GoodEtale.hart_of_flat) | (exact GlobalTheory.GoodEtale.hart_of_flat) | (intros; apply GlobalTheory.GoodEtale.hart_of_flat  <;> assumption)
