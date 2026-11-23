import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiDeterminantElementProperty
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_determinant_element_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) ι (lam : C), IsIota C D τ N ι → ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) = (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) → ∃ (Δ : RL p O Λ) (c : (Λ →+* O) → C), IsDetElt ε ψ N Δ ∧ HasOrders C ε N Δ D.lieRank c ∧ v (c τ) = v lam * v (algebraMap O C (WittVector.fontaineTheta O p (nu ε))) ^ D.lieRank τ := by
  first | exact @GlobalTheory.DetInv.exists_detElt_lieRank | exact GlobalTheory.DetInv.exists_detElt_lieRank | (intros; apply GlobalTheory.DetInv.exists_detElt_lieRank <;> assumption)
