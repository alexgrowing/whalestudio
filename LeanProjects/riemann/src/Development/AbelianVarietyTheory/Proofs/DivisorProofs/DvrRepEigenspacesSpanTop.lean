import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOfJointEigenvalueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingSemisimpleEigenspacesSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarRepCommuteAndAnnihilateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparableAnnihilatingPolyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomUniqueAdicCompleteStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem eigenspaces_span_of_integral_action : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), (⨆ σ : Λ →+* O, eig C (⇑ρ) σ) = ⊤ := by
  intro p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _ h ρ
  have hscal : ∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = padicToO p O c • (1 : Matrix (Fin h) (Fin h) O) :=
    fun c => (GlobalTheory.T.padic_ring_hom_unique_adic_complete p O).2 h (ρ.comp (algebraMap ℤ_[p] Λ)) c
  have hkill := GlobalTheory.T.scalar_rep_commute_and_annihilate C O Λ h ℤ_[p] (padicToO p O) ρ hscal
  have hdiag := GlobalTheory.T.commuting_semisimple_eigenspaces_span C (Fin h → C) Λ
    (fun a => Matrix.toLin' ((ρ a).map (algebraMap O C))) hkill.1 (fun a => by
      obtain ⟨f, hf, hsep⟩ := GlobalTheory.T.exists_separable_annihilating_poly p C ((algebraMap O C).comp (padicToO p O)) Λ a
      exact ⟨f.map ((algebraMap O C).comp (padicToO p O)), hsep, hkill.2 a f hf⟩)
  refine eq_top_iff.2 (hdiag ▸ iSup_le fun χ => ?_)
  by_cases hne : (⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C))) (χ a)) = ⊥
  · rw [hne]; exact bot_le
  · obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_ring_hom_of_joint_eigenvalue C v O Λ h hv ρ χ hne
    have hχ : χ = fun a => algebraMap O C (σ a) := funext fun a => (hσ a).symm
    subst hχ
    exact le_iSup_of_le σ le_rfl

end GlobalTheory
