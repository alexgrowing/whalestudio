import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemUnitsLocalKummerNormsOfBaseChangeNorm
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_unitsLocalKummerNorms_of_baseChange_norm : ∀ (p : ℕ) (F E L : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Field L] [Algebra F L] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ x : Fˣ, TNorm F E L (x : F) → x ∈ kNorm p (algebraMap F L) δ := by
  first | exact @GlobalTheory.CNorm.mem_kNorm_of_tNorm | exact GlobalTheory.CNorm.mem_kNorm_of_tNorm | (intros; apply GlobalTheory.CNorm.mem_kNorm_of_tNorm <;> assumption)
