import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateUnramifiedDegreeOne
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_unramified_degree_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {Ωv : Type} [Field Ωv] [ValuativeRel Ωv] [TopologicalSpace Ωv] [IsValuativeTopology Ωv]
    [Algebra F Ωv] [ValuativeExtension F Ωv] [IsSepClosure F Ωv] [IsSepClosed Ωv]
    {π : 𝒪[F]} (hπ : Irreducible π) {f : PowerSeries 𝒪[F]} (hf : IsLubinTateSeries π f)
    (u : 𝒪[F]ˣ) (τ : Ωv ≃ₐ[F] Ωv), unramifiedDegree F Ωv τ = 1 →
    (∀ n, ∀ x ∈ lubinTateTorsion Ωv (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = (u : 𝒪[F]) • x) →
    ∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension F Ωv),
    ((localArtinMap F Ωv (unitsIncl F u⁻¹) ⟨y, hy⟩ : maximalAbelianExtension F Ωv) : Ωv) = τ y := by
  first | exact @GlobalTheory.CompanionTheory.LTLink.lt_local_artin_inertia | exact GlobalTheory.CompanionTheory.LTLink.lt_local_artin_inertia | (intros; apply GlobalTheory.CompanionTheory.LTLink.lt_local_artin_inertia <;> assumption)
