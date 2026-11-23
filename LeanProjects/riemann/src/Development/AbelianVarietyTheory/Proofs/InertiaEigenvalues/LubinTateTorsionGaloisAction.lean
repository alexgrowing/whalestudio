import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.LubinTateReciprocity
import GroundTheory.LocalFields.Existence
import GroundTheory.LocalFields.KroneckerWeber
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem localArtinMap_unitUniformizerPow_lubinTateTorsion
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (Ω : Type) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [Algebra K Ω]
    [ValuativeExtension K Ω] [IsSepClosure K Ω] {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]}
    (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) (k : ℤ) (n : ℕ) (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) :
    x ∈ lubinTateTorsion Ω (hπ := hπ) hf n →
    ∃ hz : x.val ∈ maximalAbelianExtension K Ω,
      ((localArtinMap K Ω (unitUniformizerPow hπ u k) ⟨x.val, hz⟩ : maximalAbelianExtension K Ω) : Ω) =
        (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x).val := by
  intro hx
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K

  have hx' : x ∈ lubinTateTorsion Ω (hπ := hπ) hf (n + 1) := by
    rw [mem_lubinTateTorsion] at hx ⊢
    rw [pow_succ', mul_smul, hx, smul_zero]
  have hab : IsAbelianGalois K (lubinTateField Ω hπ hf (n + 1) ⊔ ⊥ : IntermediateField K Ω) := by
    rw [sup_bot_eq]
    exact isAbelianGalois_of_mul_comm _ (lubinTateField_mul_comm hπ hf (n + 1))
  have hmem : x.val ∈ (lubinTateField Ω hπ hf (n + 1) ⊔ ⊥ : IntermediateField K Ω) :=
    le_sup_left (a := lubinTateField Ω hπ hf (n + 1)) (val_mem_lubinTateField hπ hf hx')
  refine ⟨le_maximalAbelianExtension _ hmem, ?_⟩
  obtain ⟨τ, hτd, hτ⟩ := exists_lubinTate_action (Ω := Ω) hπ hf n.succ_pos u k
  have h := restrictAb_localArtinMap_lubinTate hπ hf n.succ_pos ⊥ bot_le u k τ hτd hτ
  have e := congrArg (fun σ => (((σ ⟨x.val, hmem⟩ :
    (lubinTateField Ω hπ hf (n + 1) ⊔ ⊥ : IntermediateField K Ω))) : Ω)) h
  rw [restrictAb_apply, AlgEquiv.restrictNormalHom_apply] at e
  rw [e, ← lubinTateGalPointMap_val, hτ x hx']

end GlobalTheory
