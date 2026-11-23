import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormDifferenceIndexIdentity
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_difference_index_identity : ∀ (p : ℕ) (A : Type) [CommGroup A] (σ : A →* A), (∀ a, σ^[p] a = a) → (nrm σ p).range.relIndex (fix σ) * ((dif σ).range.map (dif σ)).relIndex (dif σ).range * pTor p (fix σ) = pIdx p (fix σ) * (dif σ).range.relIndex (nrm σ p).ker * Nat.card ↥((dif σ).range ⊓ fix σ) := by
  first | exact @GlobalTheory.CNorm.herb_index_identity | exact GlobalTheory.CNorm.herb_index_identity | (intros; apply GlobalTheory.CNorm.herb_index_identity <;> assumption)
