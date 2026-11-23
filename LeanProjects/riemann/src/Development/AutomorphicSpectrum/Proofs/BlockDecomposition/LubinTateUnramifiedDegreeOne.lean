import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink

theorem lt_local_artin_inertia : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {Ωv : Type} [Field Ωv] [ValuativeRel Ωv] [TopologicalSpace Ωv] [IsValuativeTopology Ωv]
    [Algebra F Ωv] [ValuativeExtension F Ωv] [IsSepClosure F Ωv] [IsSepClosed Ωv]
    {π : 𝒪[F]} (hπ : Irreducible π) {f : PowerSeries 𝒪[F]} (hf : IsLubinTateSeries π f)
    (u : 𝒪[F]ˣ) (τ : Ωv ≃ₐ[F] Ωv), unramifiedDegree F Ωv τ = 1 →
    (∀ n, ∀ x ∈ lubinTateTorsion Ωv (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = (u : 𝒪[F]) • x) →
    ∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension F Ωv),
    ((localArtinMap F Ωv (unitsIncl F u⁻¹) ⟨y, hy⟩ : maximalAbelianExtension F Ωv) : Ωv) = τ y := by
  intro F _ _ _ _ Ωv _ _ _ _ _ _ _ _ π hπ f hf u τ hτd hτ y hy
  obtain ⟨L, _, _, hyL⟩ := exists_finite_abelian_mem hy
  obtain ⟨n, m, h⟩ := exists_le_lubinTateField_sup_unramifiedTower hπ hf L
  have hE := isUnramifiedSubextension_unramifiedTower (K := F) (Ω := Ωv) m
  have := hE.1
  have := hE.isGalois
  have hab := isAbelianGalois_lubinTateField_sup hπ hf n.succ_pos hE
  have key := restrictAb_localArtinMap_lubinTate hπ hf n.succ_pos (unramifiedTower F Ωv m)
    hE.le_maximalUnramifiedExtension u⁻¹ 0 τ (by rw [hτd]; simp)
    (by intro x hx; rw [inv_inv]; exact hτ _ x hx)
  have hx : unitUniformizerPow hπ u⁻¹ 0 = unitsIncl F u⁻¹ := by
    rw [unitUniformizerPow_eq, zpow_zero, one_mul]
  rw [hx] at key
  have h2 := congrArg (fun σ => ((σ ⟨y, h hyL⟩ : (lubinTateField Ωv hπ hf (n + 1) ⊔ unramifiedTower F Ωv m : IntermediateField F Ωv)) : Ωv)) key
  simp only [restrictAb_apply, AlgEquiv.restrictNormalHom_apply] at h2
  exact h2

end GlobalTheory.CompanionTheory.LTLink
