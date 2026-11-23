import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolLocalizationAwayStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolTransferRingMapsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonLocalizationModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfGluedPullbacksReducedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackCoverModelsSchemeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationGluesOverCoverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianGluesOverCoverStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.PolGlue

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (f : B →+* C) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem ringHom_eq_of_dedFrac {A B F : Type} [CommRing A] [CommRing B] [Field F] {ω : B →+* F} (hω : Models.IsDedFrac ω)
    {f g : A →+* B} (e : ω.comp f = ω.comp g) : f = g := by
  obtain ⟨-, -, hfr⟩ := hω
  letI := ω.toAlgebra
  ext x
  exact IsFractionRing.injective B F (congrArg (fun k => k x) e)

theorem exists_charts_of_pol (hPM : PolMapSt) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} {I : Type} [Finite I] {R : I → Type} [∀ i, CommRing (R i)]
    {a : I → 𝓞 c.F} {b : ∀ i, 𝓞 c.F →+* R i} {ω : ∀ i, R i →+* c.F} (C : ∀ i, Model Xo c (ω i)) (φ : InvFun (𝓞 E))
    (m : ℕ) (BD : ∀ i, EffCartierData (C i).X) (hφ : IsTwInv H φ) (hcov : IsCover (algebraMap (𝓞 c.F) c.F) R a b ω)
    (hpol : ∀ i, IsPol φ m (C i) (BD i)) :
    ∃ (Z : GMod Xo c) (u : ∀ i, (C i).X ⟶ Z.X), ∀ i, IsChartOf Z (C i) (a i) (b i) (u i) := by
  obtain ⟨hβ, hR, hspan⟩ := hcov
  have hD : ∀ i, Models.IsDedFrac (ω i) := fun i => (hR i).1
  have hωb : ∀ i, (ω i).comp (b i) = algebraMap (𝓞 c.F) c.F := fun i => (hR i).2.1
  have hloc : ∀ i, @IsLocalization.Away _ _ (a i) (R i) _ (b i).toAlgebra := fun i => (hR i).2.2
  have hft : Algebra.FiniteType ℤ (𝓞 c.F) := by
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : NumberField c.F := ⟨⟩
    infer_instance
  choose ω' h hω'1 hω'2 hD' hft' hopen hsq hsw using fun i k =>
    GlobalTheory.T.exists_common_localization_model (algebraMap (𝓞 c.F) c.F) (a i) (a k) (b i) (b k) (ω i) (ω k) hβ (hD i) (hD k) (hωb i) (hωb k) (hloc i)
      (hloc k) hft
  choose C' BD' v hv hvj hpol' hBD' using fun i k =>
    GlobalTheory.T.isPol_localization_away (C i) (BD i) φ m (b i (a k)) (ω' i k) (hD i) (hD' i k) (hω'1 i k) (hpol i)
  choose s hs using fun i k => hsw i k (ω' k i) (hω'1 k i)
  choose θ hθs hθj hθBD using fun i k =>
    GlobalTheory.T.isPol_transfer_ring_maps hPM (C' k i) (C' i k) (BD' k i) (BD' i k) φ m (s i k) (s k i) (hD' k i) (hD' i k) (hft' k i) (hft' i k) hφ
      (hs i k) (hs k i) (hpol' k i) (hpol' i k)
  have e1 : ∀ i k, (s i k).comp (algebraMap (R k) (Localization.Away (b k (a i)))) = h i k := fun i k =>
    ringHom_eq_of_dedFrac (hD' i k) (by rw [← RingHom.comp_assoc, hs i k, hω'1 k i, hω'2 i k])
  have e2 : ∀ i k, (s i k).comp (h k i) = algebraMap (R i) (Localization.Away (b i (a k))) := fun i k =>
    ringHom_eq_of_dedFrac (hD' i k) (by rw [← RingHom.comp_assoc, hs i k, hω'2 k i, hω'1 i k])
  have ha : ∀ i k, IsPullback (v i k) (((θ i k).hom ≫ v k i) ≫ (C k).s) ((C i).s ≫ spMap (b i)) (spMap (b k)) := by
    intro i k
    have e : ((θ i k).hom ≫ v k i) ≫ (C k).s = (C' i k).s ≫ spMap (h i k) := by
      rw [Category.assoc, (hv k i).w, ← Category.assoc, hθs, Category.assoc, spMap_comp', e1]
    rw [e]
    exact (hv i k).paste_vert (hsq i k)
  have hb : ∀ i k, IsPullback ((θ i k).hom ≫ v k i) (v i k ≫ (C i).s) ((C k).s ≫ spMap (b k)) (spMap (b i)) := by
    intro i k
    refine ((hv k i).paste_vert (hsq k i)).of_iso (θ i k).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
      rw [(hv i k).w, ← e2, ← spMap_comp']
      rw [← Category.assoc ((C' i k).s), ← hθs]
      simp
    · simp
    · simp
  have dp := fun i => ModelRelCompare.densePart (C i) (hD i)
  obtain ⟨A, F, ψ, hψ, hpsq⟩ := GlobalTheory.T.isIso_of_glued_pullbacks_reduced (fun i => Sp (R i)) (fun i => (C i).X) (fun i => spMap (b i))
    (fun i => (C i).s) (fun i k => (C' i k).X) v (fun i k => (θ i k).hom ≫ v k i) (fun i => (C i).j)
    (fun i k => (C' i k).j) (fun i => hopen i i) ha hb (fun i => (dp i).2.1) (fun i => (dp i).2.2.1)
    (fun i => (dp i).2.2.2.2.2.1) hvj (fun i k => by rw [← Category.assoc, hθj, hvj])
  have hjc : ∀ i k, (C i).j ≫ ψ i = (C k).j ≫ ψ k := fun i k => by
    rw [← hvj i k, Category.assoc, (hpsq i k).w, ← Category.assoc, ← Category.assoc, hθj, hvj]
  obtain ⟨hcv, hN, hF, hZ, hj⟩ := GlobalTheory.T.pullback_cover_models_scheme C A F ψ ⟨hβ, hR, hspan⟩ hψ hjc
  have hI : Nonempty I := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    rw [Set.range_eq_empty, Ideal.span_empty] at hspan
    exact bot_ne_top hspan
  obtain ⟨i₀⟩ := hI
  have oψ : ∀ i, IsOpenImmersion (ψ i) := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hψ i).flip (hopen i i)
  have tr := fun i => TripleGlueMap.exists_transport (ψ i).isoOpensRange (C i).t
  choose tU _ mU using tr
  have ofeq : ∀ i, Nonempty (SABMap (C i₀).oF.t (C i).oF.t (𝟙 _)) := fun i => by
    obtain ⟨n, -⟩ := exists_sabMap_of_base_eq (C i₀).m0.toSABMap (Category.id_comp _).symm
    obtain ⟨m', -⟩ := ObjMaps.exists_sab_cancel (C i).m0.toSABMap n
    exact ⟨m'⟩
  have aU : ∀ i, Nonempty (SABMap (C i₀).oF.t (tU i) ((C i).j ≫ (ψ i).isoOpensRange.hom)) := fun i => by
    obtain ⟨n₁⟩ := ofeq i
    obtain ⟨n₂, -⟩ := ObjMaps.exists_sab_comp (C i).m n₁
    obtain ⟨n₃, -⟩ := ObjMaps.exists_sab_comp (mU i).some n₂
    obtain ⟨n₄, -⟩ := exists_sabMap_of_base_eq n₃ (by rw [Category.id_comp])
    exact ⟨n₄⟩
  obtain ⟨t, -, n, -⟩ := exists_sab_glue_of_common_generic semiAbelian_hom_extends_uniquely_dvr E H A (Xo.XF c)
    ((C i₀).j ≫ ψ i₀) (C i₀).oF.t I (fun i => (ψ i).opensRange) (fun i => (C i).j ≫ (ψ i).isoOpensRange.hom) tU
    (fun i => (aU i).some) ⟨i₀⟩ ⟨hN, hZ⟩ (hj i₀).1 (hj i₀).2.1 (hj i₀).2.2.1 (hj i₀).2.2.2 (C i₀).oF.proper
    (top_le_iff.1 fun x _ => by
      obtain ⟨i, y, rfl⟩ := hcv x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, y, rfl⟩)
    (fun i => by rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, hjc])
  have nC : ∀ i, Nonempty (SABMap (C i).t t (ψ i)) := fun i => by
    obtain ⟨n₁, -⟩ := ObjMaps.exists_sab_comp (n i) (mU i).some
    obtain ⟨n₂, -⟩ := exists_sabMap_of_base_eq n₁ (Scheme.Hom.isoOpensRange_hom_ι _)
    exact ⟨n₂⟩
  have hproj := GlobalTheory.T.polarization_glues_over_cover C BD φ m A F t ψ (fun i k => (C' i k).X) v (fun i k => (θ i k).hom ≫ v k i)
    ⟨hβ, hR, hspan⟩ hψ hpsq nC hpol (fun i k => by
      rw [← hBD', Scheme.IdealSheafData.comap_comp, ← hBD', hθBD])
  exact GlobalTheory.T.semiabelian_glues_over_cover C A F ψ t (fun i => (nC i).some) i₀ ⟨hβ, hR, hspan⟩ hψ hjc hN hproj hF

end GlobalTheory.PolGlue
