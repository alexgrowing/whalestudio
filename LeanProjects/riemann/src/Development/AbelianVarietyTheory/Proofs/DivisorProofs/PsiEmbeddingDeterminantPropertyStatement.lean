import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEmbeddingDeterminantProperty
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_embedding_determinant_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ₀ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (γ : O ≃+* O), IsIsom C v γ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) ι (lam : C), IsIota C D ((γ : O →+* O).comp τ₀) N ι → lam ≠ 0 → ι '' (detLattice C (actT D) ((γ : O →+* O).comp τ₀) N : Set (detLine C (actT D) ((γ : O →+* O).comp τ₀) N)) = (fun w => lam • w) '' (detLattice C (actH D) ((γ : O →+* O).comp τ₀) N : Set (detLine C (actH D) ((γ : O →+* O).comp τ₀) N)) → Real.log (v lam) = N * κ₀ + ∑ᶠ σ, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * κ σ := by
  first | exact @GlobalTheory.DetInv.detConst_linear_isom | exact GlobalTheory.DetInv.detConst_linear_isom | (intros; apply GlobalTheory.DetInv.detConst_linear_isom <;> assumption)
