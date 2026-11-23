import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthCokerLsmulEqLengthKerAddSum
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_coker_lsmul_eq_length_ker_add_sum' : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A)), (∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M], (∀ p ∈ Module.support A M, p ∈ P ∨ p.asIdeal = IsLocalRing.maximalIdeal A) → Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) ≠ ⊤ ∧ Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) + ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) := by
  first | exact @GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum | exact GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum | (intros; apply GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum <;> assumption)
