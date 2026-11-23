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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalArtinMapUniqueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalArtinCompatibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateUnramifiedDegreeOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLeIffNormEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqFieldStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSepClosureOfRangeEqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBridgeLubinTateFieldStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisActionStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink

theorem link : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (χ : ↥(GK Bw.Kw) →* (↥Bw.Kw.1)ˣ), IsLTChar Bw.Kw χ →
    ∀ (φ : w.adicCompletion E →+* Om l), Continuous φ →
      (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) →
    ∀ (x : (w.adicCompletion E)ˣ) (σ : ↥(Dec (F := E) A)), IsUnitAt w x → (σ : G E Ω) ∈ Ine (F := E) A →
      art (localIdele E w x) = toAb E Ω σ →
      (((χ (Bw.e σ) : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1) : Om l) = φ (x : w.adicCompletion E) := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hI art hart χ hχ φ hφ hφj x σ hx hσ hxσ
  letI algF : Algebra (w.adicCompletion E) (Om l) := φ.toAlgebra
  have hmap : ∀ y, algebraMap (w.adicCompletion E) (Om l) y = φ y := fun _ => rfl
  have hr : Set.range (algebraMap (w.adicCompletion E) (Om l)) = (Bw.Kw.1 : Set (Om l)) :=
    GlobalTheory.T.local_embedding_range_eq_field Bw w φ hφ hφj
  haveI hsep : IsSepClosure (w.adicCompletion E) (Om l) := GlobalTheory.T.is_sep_closure_of_range_eq Bw.Kw hr
  haveI hext : ValuativeExtension (w.adicCompletion E) (Om l) := ⟨fun a b => by
    rw [GroundTheory.PAdicHodge.CyclNorms.vle_iff_norm_le]
    exact (GlobalTheory.T.valuation_le_iff_norm_embedding φ hφ a b).symm⟩
  haveI hclosed : IsSepClosed (Om l) := IsSepClosure.sep_closed (w.adicCompletion E)
  haveI halg : Algebra.IsAlgebraic (w.adicCompletion E) (Om l) := hsep.separable.isAlgebraic
  obtain ⟨π, hπ, H⟩ := GlobalTheory.T.exists_uniformizer_galois_action hχ hr
  let g' := Bw.e σ
  have hfix : ∀ y, (g' : GQ l) (algebraMap (w.adicCompletion E) (Om l) y) = algebraMap (w.adicCompletion E) (Om l) y := by
    intro y
    have hy : algebraMap (w.adicCompletion E) (Om l) y ∈ Bw.Kw.1 := by
      have : algebraMap (w.adicCompletion E) (Om l) y ∈ (Bw.Kw.1 : Set (Om l)) := hr ▸ ⟨y, rfl⟩
      exact this
    exact g'.2 ⟨_, hy⟩
  let g : Om l ≃ₐ[w.adicCompletion E] Om l := { (g' : GQ l).toRingEquiv with commutes' := hfix }
  have hg : ∀ y, g y = (g' : GQ l) y := fun _ => rfl
  obtain ⟨u, hu, hact⟩ := H g g' hg
  have hdeg : unramifiedDegree (w.adicCompletion E) (Om l) g = 1 := GlobalTheory.T.local_bridge_lubin_tate_field Bw hI σ hσ g hg
  have hloc := GlobalTheory.T.lubin_tate_unramified_degree_one hπ (isLubinTateSeries_ltPoly π) u g hdeg hact
  have hres := fun (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L] =>
    GlobalTheory.T.local_global_artin_compatible w Bw.j (fun y => (hφj y).symm) (unitsIncl _ u⁻¹) (σ : G E Ω) g
      (fun z => by rw [hg]; exact Bw.e_comm σ z) hloc L
  have h1 : art (localIdele E w (unitsIncl _ u)) = toAb E Ω σ := by
    rw [GlobalTheory.T.global_artin_map_unique art hart]
    have hb : ∀ a b : Gab E Ω, (∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L],
        PositivityTheory.FamInh.res L a = PositivityTheory.FamInh.res L b) → a = b := by
      intro a b h
      have := PositivityTheory.FamInh.mem_of_forall_res (H := ⊥) (g := a * b⁻¹) (by simpa using isClosed_singleton)
        fun L _ _ _ => by rw [map_mul, map_inv, h L, mul_inv_cancel]
      exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 this)
    refine hb _ _ fun L _ _ => ?_
    rw [hres L, MonoidHom.inv_apply, map_inv, map_inv]
    simp
  have h2 : unitsIncl _ u = x :=
    GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art hart w (h1.trans hxσ.symm)
  rw [← hu, ← h2]
  rfl

end GlobalTheory.CompanionTheory.LTLink
