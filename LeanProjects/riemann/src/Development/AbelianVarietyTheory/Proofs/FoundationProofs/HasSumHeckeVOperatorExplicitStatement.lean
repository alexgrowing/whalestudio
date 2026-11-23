import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeVOperatorExplicit
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_heckeVOperatorExplicit : ∀ (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < q → (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) → ∀ τ : ℍ, HasSum (fun m => (if q ∣ m then a (m / q) else 0) • Function.Periodic.qParam 1 τ ^ m) (GlobalTheory.Hk.vOp q f τ) := by
  first | exact @GlobalTheory.Hk.vOp_hasSum | exact GlobalTheory.Hk.vOp_hasSum | (intros; apply GlobalTheory.Hk.vOp_hasSum <;> assumption)
