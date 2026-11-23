import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTorsionGaloisAction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.LubinTateReciprocity
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_torsion_galois_action : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (Ω : Type) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [Algebra K Ω]
    [ValuativeExtension K Ω] [IsSepClosure K Ω] {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]}
    (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) (k : ℤ) (n : ℕ) (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)),
    x ∈ lubinTateTorsion Ω (hπ := hπ) hf n →
    ∃ hz : x.val ∈ maximalAbelianExtension K Ω,
      ((localArtinMap K Ω (unitUniformizerPow hπ u k) ⟨x.val, hz⟩ : maximalAbelianExtension K Ω) : Ω) =
        (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x).val := by
  first | exact @GlobalTheory.localArtinMap_unitUniformizerPow_lubinTateTorsion | exact GlobalTheory.localArtinMap_unitUniformizerPow_lubinTateTorsion | (intros; apply GlobalTheory.localArtinMap_unitUniformizerPow_lubinTateTorsion <;> assumption)
