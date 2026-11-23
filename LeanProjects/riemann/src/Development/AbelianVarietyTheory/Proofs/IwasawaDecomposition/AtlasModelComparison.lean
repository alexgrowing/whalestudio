import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMorphismOfStalkMapsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLocalRingPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFractionRingStalkGenericStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

set_option autoImplicit false

namespace GlobalTheory.MapLoc

theorem exists_gen (X : Scheme.{0}) (x : X) (hd : IsDomain (X.presheaf.stalk x)) :
    ∃ ξ : X, ξ ⤳ x ∧ ∀ y, y ⤳ x → ξ ⤳ y := by
  let η : PrimeSpectrum (X.presheaf.stalk x) := ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨X.fromSpecStalk x η, ?_, ?_⟩
  · have h1 : η ⤳ IsLocalRing.closedPoint (X.presheaf.stalk x) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal _) ≤ _ from bot_le)
    have := h1.map (X.fromSpecStalk x).continuous
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  · intro y hy
    have : y ∈ Set.range (X.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact hy
    obtain ⟨q, rfl⟩ := this
    exact ((PrimeSpectrum.le_iff_specializes η q).1 (show (⊥ : Ideal _) ≤ _ from bot_le)).map
      (X.fromSpecStalk x).continuous

theorem isFractionRing_residue : ∀ (X : Scheme.{0}) (x ξ : X) (e : ξ ⤳ x), IsDomain (X.presheaf.stalk x) →
    (∀ y, y ⤳ ξ → y = ξ) →
    @IsFractionRing (X.presheaf.stalk x) _ (X.residueField ξ) _
      (RingHom.toAlgebra (X.presheaf.stalkSpecializes e ≫ X.residue ξ).hom) :=
  GlobalTheory.T.isFractionRing_stalk_generic

theorem spMap_cancel {R K A : Type} [CommRing R] [CommRing K] [CommRing A] (f : R →+* K) (hf : Function.Injective f)
    (u v : Sp R ⟶ Sp A) (h : spMap f ≫ u = spMap f ≫ v) : u = v := by
  rw [← Spec.map_preimage u, ← Spec.map_preimage v] at h ⊢
  congr 1
  have e := Spec.map_injective ((Spec.map_comp _ _).trans (h.trans (Spec.map_comp _ _).symm))
  ext a
  exact hf (congrArg (fun φ => φ.hom a) e)

end GlobalTheory.MapLoc

open GlobalTheory.MapLoc in
theorem GlobalTheory.DRFlag.exists_mapsTo : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (Z : Mdl Y i₀), p.Prime → (p : ℂ) ∈ W.nonunits → Geo (Y i) π → i.c.F ≤ Z.i.c.F → (∀ σ, ty σ ⊆ Z.ty σ) → LocMaps Z A → ∃ h, MapsTo Z A h := by
  intro E _ _ _ H Dw Xo p W Y i₀ i X π ty A Z hp hW hgeo hF hty hloc

  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z.X := (geoOf Z).normal
  have : IsDiscreteValuationRing (Z.i.c.V W) := isDiscreteValuationRing_V _ W hp hW
  have hZp : IsProper Z.s := by
    have := projProper _ _ _ (geoOf Z).proj
    rwa [Z.π_s] at this
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  have : CompactSpace Z.X := QuasiCompact.compactSpace_of_compactSpace Z.s
  have : IsNoetherian Z.X := {}
  have hXp : IsProper (π ≫ (Y i).s) := projProper _ _ _ hgeo.proj
  have hopen : IsOpen Z.opn := by
    rw [← Z.cover]
    exact isOpen_iUnion fun a => (Z.U a).1.isOpen
  have hdom : ∀ x : Z.X, IsDomain (Z.X.presheaf.stalk x) := fun x => (hn x).1

  choose g hgx hgmin using fun x : Z.X => exists_gen Z.X x (hdom x)
  have hgo : ∀ x, g x ∈ Z.opn := fun x => by
    obtain ⟨g', hg', hg'x⟩ := GlobalTheory.ShFam.EigLoc.exists_generisation hopen Z.dense x
    exact (hgmin x g' hg'x).mem_open hopen hg'
  have hgen : ∀ x y, y ⤳ g x → y = g x := fun x y hy =>
    (hy.antisymm (hgmin x y (hy.trans (hgx x)))).eq

  let f : ∀ x : Z.X, Z.X.presheaf.stalk x →+* Z.X.residueField (g x) := fun x =>
    (Z.X.presheaf.stalkSpecializes (hgx x) ≫ Z.X.residue (g x)).hom
  have hfr : ∀ x, @IsFractionRing (Z.X.presheaf.stalk x) _ (Z.X.residueField (g x)) _ (f x).toAlgebra := fun x =>
    isFractionRing_residue Z.X x (g x) (hgx x) (hdom x) (hgen x)
  have hinj : ∀ x, Function.Injective (f x) := fun x => by
    letI := (f x).toAlgebra
    haveI := hfr x
    exact IsFractionRing.injective (Z.X.presheaf.stalk x) (Z.X.residueField (g x))
  have key : ∀ x, spMap (f x) ≫ Z.X.fromSpecStalk x = Z.X.fromSpecResidueField (g x) := fun x => by
    show Spec.map (_ ≫ _) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl

  have Hy : ∀ ξ : Z.opn, ∃ y : Sp (Z.X.residueField ξ.1) ⟶ X, NatTo Z A (Z.X.fromSpecResidueField ξ.1) y ∧
      ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] [Algebra R (Z.X.residueField ξ.1)]
        [IsFractionRing R (Z.X.residueField ξ.1)] (z : Sp R ⟶ Z.X),
        spMap (algebraMap R (Z.X.residueField ξ.1)) ≫ z = Z.X.fromSpecResidueField ξ.1 →
        ∃ z' : Sp R ⟶ X, spMap (algebraMap R (Z.X.residueField ξ.1)) ≫ z' = y := fun ξ =>
    hloc _ _ (by
      rintro _ ⟨q, rfl⟩
      exact Set.mem_of_eq_of_mem (Scheme.fromSpecResidueField_apply ξ.1 _) ξ.2)
  choose y hyN hyE using Hy

  have Hh : ∀ x : Z.X, ∃ z' : Sp (Z.X.presheaf.stalk x) ⟶ X, spMap (f x) ≫ z' = y ⟨g x, hgo x⟩ := fun x => by
    letI := (f x).toAlgebra
    haveI := hfr x
    haveI := hdom x
    haveI := (hn x).2
    exact hyE ⟨g x, hgo x⟩ (Z.X.presheaf.stalk x) (Z.X.fromSpecStalk x) (key x)
  choose h hh using Hh
  have hh' : ∀ x ξ (e : ξ ⤳ x), g x = ξ → ∀ hξ : ξ ∈ Z.opn,
      Spec.map (Z.X.presheaf.stalkSpecializes e ≫ Z.X.residue ξ) ≫ h x = y ⟨ξ, hξ⟩ := by
    rintro x ξ e rfl hξ
    exact hh x

  let b : i.c.V W →+* Z.i.c.V W :=
    ((IntermediateField.inclusion hF).toRingHom.comp (i.c.V W).subtype).codRestrict (Z.i.c.V W) fun x => x.2
  have hovr : ∀ {K : Type} [Field K] (w : Sp K ⟶ Z.X) (y' : Sp K ⟶ X), NatTo Z A w y' →
      y' ≫ π ≫ (Y i).s = w ≫ Z.s ≫ spMap b := by
    rintro K _ w y' ⟨τ, mu, u, ⟨b', π', r, hb', h1, h2, -⟩, he, -, -⟩
    have eb : b' = b := RingHom.ext fun v => Subtype.ext (Subtype.ext (hb' v))
    subst eb
    rw [← Category.assoc, he, ← h1, ← Z.π_s]
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% h2]
  have hover : ∀ x, h x ≫ π ≫ (Y i).s = Z.X.fromSpecStalk x ≫ Z.s ≫ spMap b := fun x => by
    apply spMap_cancel (f x) (hinj x)
    rw [← Category.assoc, hh x]
    exact (hovr (Z.X.fromSpecResidueField (g x)) (y ⟨g x, hgo x⟩) (hyN ⟨g x, hgo x⟩)).trans (by rw [← key x]; exact Category.assoc _ _ _)

  obtain ⟨gg, hgg⟩ := GlobalTheory.T.exists_morphism_of_stalk_maps (Sp (i.c.V W)) Z.X X (Z.s ≫ spMap b) (π ≫ (Y i).s) h inferInstance inferInstance
    inferInstance hn hover (by
      intro x ξ e hξ
      have hxg : g x = ξ := hξ _ (hgmin x ξ e)
      have hξg : g ξ = ξ := hξ _ (hgx ξ)
      have hξo : ξ ∈ Z.opn := hxg ▸ hgo x
      have hi : Function.Injective (Z.X.residue ξ).hom := by
        letI := (Z.X.presheaf.stalkSpecializes (specializes_refl ξ) ≫ Z.X.residue ξ).hom.toAlgebra
        haveI := isFractionRing_residue Z.X ξ ξ (specializes_refl ξ) (hdom ξ) hξ
        have := IsFractionRing.injective (Z.X.presheaf.stalk ξ) (Z.X.residueField ξ)
        rwa [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at this
      haveI : IsIso (Z.X.residue ξ) := (ConcreteCategory.isIso_iff_bijective _).2 ⟨hi, Scheme.residue_surjective _ _⟩
      rw [← cancel_epi (Spec.map (Z.X.residue ξ)), ← Category.assoc, ← Spec.map_comp, hh' x ξ e hxg hξo]
      have := hh' ξ ξ (specializes_refl ξ) hξg hξo
      rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at this
      exact this.symm)

  refine ⟨gg, fun k _ w hw => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x, w (IsLocalRing.closedPoint k) = x := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.ShFam.EigLoc.exists_stalk_factor w x (hx ▸ specializes_rfl)
  have hxo : x ∈ Z.opn := hx ▸ hw ⟨_, rfl⟩
  have e1 : w ≫ gg = spMap ψ ≫ h x := by rw [← hψ, Category.assoc, hgg]
  rw [e1, ← hψ]
  refine GlobalTheory.T.atlas_local_ring_points E H Dw Xo p W Y i₀ i X π ty A Z (Z.X.presheaf.stalk x) (Z.X.residueField (g x)) k (f x) ψ
    (Z.X.fromSpecStalk x) (h x) hF hty (hinj x) (by rw [Scheme.fromSpecStalk_closedPoint]; exact hxo) ?_
  rw [key x, hh x]
  exact hyN ⟨g x, hgo x⟩
