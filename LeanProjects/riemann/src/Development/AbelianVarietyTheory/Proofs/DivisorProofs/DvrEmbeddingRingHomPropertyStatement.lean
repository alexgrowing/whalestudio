import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrEmbeddingRingHomProperty
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_embedding_ring_hom_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ : Λ →+* O, ∃ s : RL p O Λ, (∀ f, IsTheta τ f → f s ≠ 0) ∧ (∀ σ f, σ ≠ τ → IsTheta σ f → f s = 0) ∧ ∀ f, IsTheta τ f → ∀ r, f r = 0 → (inA (xi ε) : RL p O Λ) ∣ s * r := by
  first | exact @GlobalTheory.DetInv.exists_sep_theta | exact GlobalTheory.DetInv.exists_sep_theta | (intros; apply GlobalTheory.DetInv.exists_sep_theta <;> assumption)
