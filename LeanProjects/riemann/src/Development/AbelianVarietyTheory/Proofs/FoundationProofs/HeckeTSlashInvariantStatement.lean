import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTSlashInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeT_slash_eq_of_slash_eq : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < N → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → (∀ γ ∈ GlobalTheory.Hk.lev N l, f ∣[k] γ = f) → ∀ γ ∈ GlobalTheory.Hk.lev N l, GlobalTheory.Hk.heckeT k q σ f ∣[k] γ = GlobalTheory.Hk.heckeT k q σ f := by
  first | exact @GlobalTheory.HkInv.heckeT_slash_invariant | exact GlobalTheory.HkInv.heckeT_slash_invariant | (intros; apply GlobalTheory.HkInv.heckeT_slash_invariant <;> assumption)
