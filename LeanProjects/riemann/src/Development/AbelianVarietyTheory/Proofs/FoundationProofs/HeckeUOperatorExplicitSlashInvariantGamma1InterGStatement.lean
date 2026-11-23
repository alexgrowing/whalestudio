import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitSlashInvariantGamma1InterGamma0
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeUOperatorExplicit_slash_invariant_gamma1InterGamma0 : ∀ (N l q : ℕ) (k : ℤ) (f : ℍ → ℂ), 0 < N → 0 < l → q.Prime → q ∣ N * l → (∀ γ ∈ GlobalTheory.Hk.lev N l, f ∣[k] γ = f) → ∀ γ ∈ GlobalTheory.Hk.lev N l, GlobalTheory.Hk.uOp q f ∣[k] γ = GlobalTheory.Hk.uOp q f := by
  first | exact @GlobalTheory.Hk.uOp_slash_lev | exact GlobalTheory.Hk.uOp_slash_lev | (intros; apply GlobalTheory.Hk.uOp_slash_lev <;> assumption)
