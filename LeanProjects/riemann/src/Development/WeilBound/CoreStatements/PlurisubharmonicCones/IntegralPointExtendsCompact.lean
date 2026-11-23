import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.TorusModelCochar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieMetricStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldPointIntegralModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalHermitianFibreStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsAbelianPartExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricHeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLieSignatureStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieSignatureNumberFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspCorrespondenceBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuesOfFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtComplexEmbedding
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AbelianPartHeightLinear
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace LevelTowerAlt

theorem integral_point_extends_compact : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L₀ : Type) [Field L₀] [NumberField L₀], 1 ≤ D.p + D.q → ∀ w ∈ Small.ptsOver L₀ (mCoordIdeal y), ∃ (L : Type) (_ : Field L) (_ : NumberField L) (e : L₀ →+* L) (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) (_ : AddCommGroup V) (_ : Module L V) (_ : Module (𝓞 L) V) (_ : IsScalarTower (𝓞 L) L V) (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V), CoordsAt 𝔐.ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) (fun p => e (w p)) ∧ 𝔐.IsLinPtOf z P MV A ∧ (∀ s, Module.finrank L (eigSp A.ρ (A.σ s)) = labelRk D s) ∧ Module.finrank (𝓞 L) A.Bq.carrier ≤ Fintype.card (CMType H) * (D.p + D.q) := by
  intro hG E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L₀ _ _ hpq w hw
  classical
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨h⟩ := GlobalTheory.T.exists_lie_metric 𝔐.X Ω K J y 𝔐.ξ inferInstance 𝔐.all 𝔐.tie 𝔐.t.G 𝔐.Li 𝔐.M
  obtain ⟨K₀, -, hQ⟩ := GlobalTheory.T.lie_metric_height_bound hG.2.2.2.2.1 E H D l Xo c Y S Ω K J y 𝔐 h hpq
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.number_field_point_integral_model 𝔐.X Ω K J y 𝔐.ξ inferInstance 𝔐.all 𝔐.tie L₀ w hw
  obtain ⟨L₁, _, _, e₁, ⟨P₁⟩⟩ := GlobalTheory.T.exists_abelian_part_extension E H 𝔐.X 𝔐.t L₀ (spMap (algebraMap (𝓞 L₀) L₀) ≫ z₀)
  obtain ⟨σ₁⟩ : Nonempty (L₁ →+* ℂ) := inferInstance
  obtain ⟨P₁c, _, mBc, _, _⟩ := GlobalTheory.T.abelian_part_base_change E H 𝔐.X 𝔐.t L₁ ℂ _ P₁ σ₁
  have hpr : IsPrincipal P₁.tB := (GlobalTheory.T.isPrincipal_base_change_iff E H L₁ ℂ σ₁ P₁.tB P₁c.tB mBc).1 (hQ _ P₁c).1
  obtain ⟨L, _, _, e₂, t', tK, ⟨m₁⟩, ⟨mP⟩⟩ := GlobalTheory.T.lie_signature_number_field hG.1.2.1 hG.1.1 E H L₁ P₁.tB hpr
    (GlobalTheory.T.abelian_part_lie_signature E H D l Xo c Y S Ω K J y 𝔐 L₁ _ P₁)
  let z : Sp (𝓞 L) ⟶ 𝔐.X := spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) ≫ z₀
  have hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ (spMap e₁ ≫ spMap (algebraMap (𝓞 L₀) L₀) ≫ z₀) := by
    have e : spMap (algebraMap (𝓞 L) L) ≫ spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) =
        spMap e₂ ≫ spMap e₁ ≫ spMap (algebraMap (𝓞 L₀) L₀) := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    simp only [z]
    rw [← Category.assoc, e]
    simp only [Category.assoc]
  have hco : CoordsAt 𝔐.ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) (fun p => (e₂.comp e₁) (w p)) := by
    rw [hz]
    exact RootHt.PullCoords.coordsAt_field e₂ (RootHt.PullCoords.coordsAt_field e₁ hz₀)
  obtain ⟨P, hP, ⟨m'⟩⟩ : ∃ P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z), IsPrincipal P.tB ∧
      Nonempty (SABMap P.tB t' (spMap (algebraMap (𝓞 L) L))) := by
    rw [hz]
    obtain ⟨P₂, -, mB2, -, -⟩ := GlobalTheory.T.abelian_part_base_change E H 𝔐.X 𝔐.t L₁ L _ P₁ e₂
    refine ⟨P₂, (GlobalTheory.T.isPrincipal_base_change_iff E H L₁ L e₂ P₁.tB P₂.tB mB2).2 hpr, ?_⟩
    obtain ⟨n⟩ : Nonempty (SABMap P₂.tB P₁.tB (𝟙 _ ≫ spMap e₂)) := by
      rw [Category.id_comp]
      exact ⟨mB2⟩
    obtain ⟨n', -⟩ := sabCancel pullCubCancel E H _ _ _ P₁.tB tK P₂.tB _ _ mP n
    obtain ⟨n'', -⟩ := sabComp pullCubComp E H _ _ _ t' tK P₂.tB _ _ m₁ n'
    rw [← Category.id_comp (spMap (algebraMap (𝓞 L) L))]
    exact ⟨n''⟩
  obtain ⟨B, MB, hB⟩ := GlobalTheory.T.principal_hermitian_fibre E H L t' P.tB m' hP
  obtain ⟨σ, hlab, -, hbij, hinj, hcard, -⟩ := GlobalTheory.T.cusp_correspondence_bound E H D l Xo c Y S Ω K J y 𝔐 L
    (spMap (algebraMap (𝓞 L) L) ≫ z)
  obtain ⟨V, _, _, _, _, MV, A, rfl, hact, hΛ, hI, ⟨MB', hB', hf⟩, hrk⟩ :=
    Lin.exists_lin 𝔐.t z P t' m' hP B MB hB σ hbij hinj
  obtain ⟨hV, -, hlat⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c (𝓞 c.F) (algebraMap _ _) Y S Ω K J y 𝔐
    (FaithfulSMul.algebraMap_injective _ _) ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩
    (fun r hr => PtHt.FrameVal.not_inFibre _ _ r hr)
  have hb : ∀ s, ∃ sL : Fin (labelRk D s) → V, LinearIndependent L sL ∧
      Submodule.span L (Set.range sL) = eigSp A.ρ (A.σ s) := fun s => by
    obtain ⟨U, hU, b, -, hfr⟩ := 𝔐.vb s ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ trivial
    have h1 : (𝔐.V s).IsFrameAt b ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ := hfr _ trivial hU
    obtain ⟨sL, -, h2⟩ := PtHt.FrameVal.values_core 𝔐 _ P.tK P.m MV A.ρ A.σ A.σ_bij.1 hact hlab hlat s b
      ⟨h1.1, (hV s).symm.trans h1.2⟩
    exact ⟨sL, h2⟩
  choose sL hli hsp using hb
  refine ⟨L, inferInstance, inferInstance, e₂.comp e₁, z, P, V, inferInstance, inferInstance, inferInstance,
    inferInstance, MV, A, hco, ⟨hact, hlab, hΛ, hI, hP, t', m', MB', hB', hf⟩, fun s => ?_, hrk.trans ?_⟩
  · rw [← hsp s, finrank_span_eq_card (hli s), Fintype.card_fin]
  · have htop := iSup_eigSp_eq_top A.ρ A.σ A.σ_bij.1 (by rw [Fintype.card_sum, ← hcard]; ring)
    have hs : Submodule.span L (Set.range fun p : (Σ s, Fin (labelRk D s)) => sL p.1 p.2) = ⊤ := by
      rw [eq_top_iff, ← htop]
      refine iSup_le fun s => ?_
      rw [← hsp s]
      exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨⟨s, i⟩, rfl⟩)
    refine (finrank_le_of_span_eq_top hs).trans ?_
    simp [Fintype.card_sigma, Fintype.sum_sum_type, mul_add]

end LevelTowerAlt
