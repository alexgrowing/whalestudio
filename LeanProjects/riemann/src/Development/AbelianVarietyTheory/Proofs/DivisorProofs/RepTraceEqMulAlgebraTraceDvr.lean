import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenDecompositionTraceMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenspacesOfRingHomsIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftMulEigenspaceFinrankOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftMulMatrixRingHomTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrRepEigenspacesSpanTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomUniqueAdicCompleteStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem finrank_eig_of_trace_eq_mul_trace : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), (∀ a, (ρ a).trace = (N : O) * padicToO p O (Algebra.trace ℤ_[p] Λ a)) → ∀ τ : Λ →+* O, Module.finrank C (eig C (⇑ρ) τ) = N := by
  intro p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _ N h ρ hρ τ
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  haveI : Module.IsTorsionFree ℤ_[p] Λ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  haveI : Module.Free ℤ_[p] Λ := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ_[p] Λ
  obtain ⟨⟨ρ', hρ'⟩, htr⟩ := GlobalTheory.T.left_mul_matrix_ring_hom_trace O ℤ_[p] Λ _ b (padicToO p O)
  have key := GlobalTheory.T.eigen_decomposition_trace_multiple C O Λ h _ N (⇑ρ) (⇑ρ') hinj
    (GlobalTheory.T.eigenspaces_of_ring_homs_independent C O Λ h ρ hinj)
    (GlobalTheory.T.dvr_rep_eigenspaces_span_top p C v O hv Λ h ρ)
    (GlobalTheory.T.eigenspaces_of_ring_homs_independent C O Λ _ ρ' hinj)
    (GlobalTheory.T.dvr_rep_eigenspaces_span_top p C v O hv Λ _ ρ')
    (fun a => by rw [hρ a, hρ', htr a]) τ
  have hτ : τ.comp (algebraMap ℤ_[p] Λ) = padicToO p O := (GlobalTheory.T.padic_ring_hom_unique_adic_complete p O).1 _
  have one := GlobalTheory.T.left_mul_eigenspace_finrank_one C O ℤ_[p] Λ _ b (padicToO p O) τ hτ
  rw [key, hρ', one, mul_one]

end GlobalTheory
