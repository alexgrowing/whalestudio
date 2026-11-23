import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CohomologyKernelModPrimePowerKilledByFixedPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyKernel_modPrimePower_killed_by_fixed_pow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l), (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) → ∃ r : ℕ, ∀ (n : ℕ) (a : G ℚ Ω → Fin 2 → Qbar l) (y : Fin 2 → Qbar l), (∀ s i, a s i ∈ c.O) → VecE c y → (∀ s, Cv n (a s) (mat W s *ᵥ y - y)) → Cob1 c n W ⊤ (fun s => ((l : ℕ) : Qbar l) ^ r • a s) := by
  first | exact @GlobalTheory.Ord2.exists_pow_smul_cob1_of_cv_mod_pow | exact GlobalTheory.Ord2.exists_pow_smul_cob1_of_cv_mod_pow | (intros; apply GlobalTheory.Ord2.exists_pow_smul_cob1_of_cv_mod_pow <;> assumption)
