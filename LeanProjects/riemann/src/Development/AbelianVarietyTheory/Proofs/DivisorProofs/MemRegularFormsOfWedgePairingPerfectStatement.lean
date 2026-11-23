import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRegularFormsOfWedgePairingPerfect
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_regularForms_of_wedge_pairing_perfect : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (d p q : ℕ), Module.finrank K Ω[K⁄k] = d → p + q = d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K B p, a * y ∈ omB k K B d) → y ∈ omB k K B q := by
  first | (exact @GlobalTheory.PD.mem_omB_of_mul_mem_omB) | (exact GlobalTheory.PD.mem_omB_of_mul_mem_omB) | (intros; apply GlobalTheory.PD.mem_omB_of_mul_mem_omB  <;> assumption)
