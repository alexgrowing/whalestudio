import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitNotLocalKummerNormOfNotPow
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_not_localKummerNorm_of_not_pow : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (ζ δ : F) (v : HeightOneSpectrum (𝓞 F)), p.Prime → IsPrimitiveRoot ζ p → (∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ) → ∃ c : (v.adicCompletion F)ˣ, c ∉ kNorm p (RingHom.id (v.adicCompletion F)) (algebraMap F (v.adicCompletion F) δ) := by
  first | exact @GlobalTheory.CNorm.exists_local_nonnorm | exact GlobalTheory.CNorm.exists_local_nonnorm | (intros; apply GlobalTheory.CNorm.exists_local_nonnorm <;> assumption)
