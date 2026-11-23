import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntTwoCocycleEqPowSmulOfReductionCoboundary
import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_z2_sub_pow_smul_mem_b2_of_reduction : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]), ContAction ρ → ∀ (r : ℕ) (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) → ∀ z ∈ Z2 ρ, (fun p => PadicInt.toZModPow r (z p)) ∈ B2 ρr → ∃ w ∈ Z2 ρ, z - (l : ℤ_[l]) ^ r • w ∈ B2 ρ := by
  first | exact @GlobalTheory.padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary | exact GlobalTheory.padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary | (intros; apply GlobalTheory.padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary <;> assumption)
