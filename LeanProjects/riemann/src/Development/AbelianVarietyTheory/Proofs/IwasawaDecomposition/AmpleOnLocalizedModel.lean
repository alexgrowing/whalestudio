import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericEmbeddingLocalizedModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmplePointsLocalizedModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalSectionFlatPreimmersionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSectionsFlatMonomorphismStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MorphismToLocalizedModelStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef

namespace GlobalTheory.DomFine

theorem model_basics : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (R : Type) [CommRing R] (a : 𝓞 c.F) (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (C : Model Xo c ω), IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ a R _ b.toAlgebra → C.j ≫ C.s = pullback.snd _ _ ≫ spMap ω ∧ IsReduced (Xo.XF c) ∧ IsLocallyNoetherian (Xo.XF c) ∧ LocallyOfFiniteType C.s ∧ IsSeparated C.s ∧ (Sp R).IsSeparated := by
  intro E _ _ _ H D l Xo c Z R _ a b ω C _ _ _
  have hprop : IsProper C.s := by
    obtain ⟨N, i, hi, e⟩ := C.proj
    have := isProper_str R N
    rw [← e]; infer_instance
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  obtain ⟨h1, -, h3⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance
  refine ⟨?_, h1, h3, inferInstance, inferInstance, inferInstance⟩
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

theorem dominates_of_fineData : FreeSt → ExtendSt → ExtAtSt → GlueSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (R : Type) [CommRing R] (a : 𝓞 c.F) (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (C : Model Xo c ω) (m : ℕ), IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ a R _ b.toAlgebra → 1 ≤ m → AmpAt C m → (∀ z : Z.X, ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ξ : Sp R' ⟶ Z.X) (t : SAB H (Sp R')) (_ : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R') t), IsCN R' ∧ ξ (closedPoint R') = z ∧ (Scheme.stalkClosedPointTo ξ).hom.Flat ∧ FineData P.D.toPre 1 ∧ FineData P.D.toPre (m ^ 2)) → Dominates Z C b := by
  intro hFr hEx hAt _ E _ _ _ H D l Xo c Z R _ a b ω C m hω hb hloc hm hAmp hpts
  have hZs : Z.j ≫ Z.s = pullback.snd _ _ ≫ spMap ω ≫ spMap b := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Z.jQ_over, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hb]
  let jX : Xo.XF c ⟶ pullback Z.s (spMap b) :=
    pullback.lift Z.j (pullback.snd _ _ ≫ spMap ω) (by rw [hZs, Category.assoc])
  have hjX : jX ≫ pullback.fst _ _ = Z.j := pullback.lift_fst _ _ _
  obtain ⟨hfo, hXn, hXnorm, hXZ, hpre, hfl, hdom, hqc, hjs, huniq⟩ :=
    GlobalTheory.T.generic_embedding_localized_model E H D l Xo c Z R a b ω C hω hb hloc jX hjX
  obtain ⟨hCj, hred, hUn, hCft, hCsep, hRsep⟩ := GlobalTheory.DomFine.model_basics E H D l Xo c Z R a b ω C hω hb hloc
  have hgs : C.j ≫ C.s = jX ≫ pullback.snd _ _ := by rw [hCj, hjs]
  have key : ∀ x : ↥(pullback Z.s (spMap b)), ∃ (V : (pullback Z.s (spMap b)).Opens) (hx : x ∈ V)
      (h : V.toScheme ⟶ C.X) (p : ↥(pullback Z.s (spMap b))) (hp : p ∈ V)
      (v : Spec ((pullback Z.s (spMap b)).presheaf.stalk p) ⟶ Xo.XF c), p ⤳ x ∧ (∀ q, q ⤳ p → q = p) ∧
        v ≫ jX = (pullback Z.s (spMap b)).fromSpecStalk p ∧ V.fromSpecStalkOfMem p hp ≫ h = v ≫ C.j := by
    intro x
    obtain ⟨R', _, _, _, ξ, y, χ, hξx, hξfl, hy, hχ, hχs, hgen⟩ :=
      GlobalTheory.T.ample_points_localized_model hFr hEx E H D l Xo c Z R a b ω C hω hb hloc m hm hAmp hpts jX hjX x
    let w₀ : Sp (FractionRing R') := closedPoint (FractionRing R')
    have hpr : (jK R' ≫ ξ) w₀ ∈ Set.range jX := ⟨y w₀, by rw [← Scheme.Hom.comp_apply, hy]⟩
    obtain ⟨W, f, v, hpW, hv, hfs, hfc⟩ := GlobalTheory.T.exists_local_section_flat_preimmersion (Sp R) _ (Xo.XF c) C.X (pullback.snd _ _) C.s jX C.j hCft hCsep hXn
      hXnorm hred hpre hfl hgs _ hpr (hgen w₀)
    have hrange : Set.range (jK R' ≫ ξ) ⊆ Set.range W.ι := by
      rintro _ ⟨w, rfl⟩
      rw [Subsingleton.elim w w₀, Scheme.Opens.range_ι]
      exact hpW
    let yW := IsOpenImmersion.lift W.ι (jK R' ≫ ξ) hrange
    have hyW : yW ≫ W.ι = jK R' ≫ ξ := IsOpenImmersion.lift_fac _ _ _
    have hext := hAt _ _ W.toScheme C.X (Sp R) (𝟙 _) W.ι f (pullback.snd _ _) C.s R' ξ yW χ inferInstance hCsep hCft
      hfs hξfl (by rw [hyW, Category.comp_id]) (by rw [hχ]; exact (hfc _ yW y (by rw [hyW, hy])).symm)
      (by rw [hχs, Category.id_comp])
    rw [hξx] at hext
    obtain ⟨V, h, hxV, hV⟩ := hext
    have hpx : (jK R' ≫ ξ) w₀ ⤳ x := by
      rw [← hξx, Scheme.Hom.comp_apply]
      exact (IsLocalRing.specializes_closedPoint _).map ξ.continuous
    have hpV : (jK R' ≫ ξ) w₀ ∈ V := hpx.mem_open V.2 hxV
    refine ⟨V, hxV, h, _, hpV, v, hpx, hgen w₀, hv, ?_⟩
    rw [hV _ (V.fromSpecStalkOfMem _ hpV) (W.fromSpecStalkOfMem _ hpW)
      (by rw [Category.comp_id, Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι])]
    exact hfc _ _ v (by rw [Scheme.Opens.fromSpecStalkOfMem_ι, hv])
  obtain ⟨F, hFs, hFj⟩ := GlobalTheory.T.exists_extension_of_local_maps_agree_at_generic_points (Sp R) _ (Xo.XF c) C.X (pullback.snd _ _) C.s jX C.j hCft hCsep hRsep hXn hXnorm hred
    hUn inferInstance hfl hgs key
  exact GlobalTheory.T.morphism_to_localized_model E H D l Xo c Z R a b ω C hω hb hloc F hFs (fun u hu => by rw [huniq u hu, hFj])

end GlobalTheory.DomFine
