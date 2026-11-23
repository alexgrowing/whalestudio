import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorExtendsDvrStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueHomExtensionSemiAbelian

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieHomOk

theorem exists_generic_model {O K : Type} [CommRing O] [Field K] (c : O →+* K) (G : Over (Sp O)) [GrpObj G]
    [IsCommMonObj G] (GK : Over (Sp K)) [GrpObj GK] (φ : GK.left ⟶ G.left)
    (h : IsGrpPullback GK G (spMap c) φ) {E : Type} [AddCommGroup E] [Module O E]
    (M : LieModel G (𝟙 _) E) :
    ∃ (EK : Type) (_ : AddCommGroup EK) (_ : Module K EK) (MK : LieModel GK (𝟙 _) EK)
      (N : LieModel G (spMap c ≫ 𝟙 _) EK) (j : E →ₛₗ[c] EK),
      (∀ x, (MK.pt x).left ≫ φ = (N.pt x).left) ∧ ∀ e, M.Lifts c (𝟙 G.left) e (N.pt (j e)) := by
  obtain ⟨EK, i1, i2, ⟨N⟩⟩ := lieModel_exists (Sp O) G K (spMap c ≫ 𝟙 _)
  have hx : spMap c ≫ 𝟙 (Sp O) = 𝟙 (Sp K) ≫ spMap c := by simp
  have gen : ∀ (y : Sp K ⟶ Sp O), spMap c ≫ 𝟙 (Sp O) = y →
      ∃ N' : LieModel G y EK, ∀ x, (N'.pt x).left = (N.pt x).left := by
    rintro y rfl
    exact ⟨N, fun _ => rfl⟩
  obtain ⟨N', hN'⟩ := gen _ hx
  obtain ⟨MK, hMK⟩ := (LiePull.lieModel_pullback _ _ G GK (spMap c) φ h K (𝟙 _) EK).1 N'
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts (Sp O) G O K c (𝟙 _) E EK M N
  exact ⟨EK, i1, i2, MK, N, j, fun x => by rw [hMK, hN'], hj⟩

theorem ext_of_spMap_injective {A B : Type} [CommRing A] [CommRing B] (d : A →+* B)
    (hd : Function.Injective d) {X Y : Scheme.{0}} (p : X ⟶ Y) [IsSeparated p] (a b : Sp A ⟶ X)
    (hab : a ≫ p = b ≫ p) (h : spMap d ≫ a = spMap d ≫ b) : a = b := by
  let X' : Over Y := Over.mk (a ≫ p)
  let Y' : Over Y := Over.mk p
  let f' : X' ⟶ Y' := Over.homMk a
  let g' : X' ⟶ Y' := Over.homMk b hab.symm
  haveI : IsSeparated Y'.hom := ‹IsSeparated p›
  let U' : Over Y := Over.mk (spMap d ≫ a ≫ p)
  let i' : U' ⟶ X' := Over.homMk (spMap d)
  have e : i' ≫ f' = i' ≫ g' := by
    ext1
    exact h
  let l := equalizer.lift i' e
  have hi : spMap d = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  haveI hcl : IsClosedImmersion (equalizer.ι f' g').left := isClosedImmersion_equalizer_ι_left _ _
  haveI : IsAffine X'.left := inferInstanceAs (IsAffine (Sp A))
  obtain ⟨hA, hs⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (equalizer.ι f' g').left
  have h2 : Function.Injective (spMap d).appTop.hom := by
    have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom d)
    have inj : Function.Injective ((Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom d).hom := by
      rw [CommRingCat.hom_comp]
      exact hd.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
    rw [← nat, CommRingCat.hom_comp] at inj
    exact Function.Injective.of_comp inj
  have hinj : Function.Injective (equalizer.ι f' g').left.appTop.hom := by
    have e2 : (spMap d).appTop = (equalizer.ι f' g').left.appTop ≫ l.left.appTop := by
      rw [hi]
      simp
    rw [e2, CommRingCat.hom_comp] at h2
    exact Function.Injective.of_comp h2
  haveI : IsIso (equalizer.ι f' g').left.appTop :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, hs⟩
  haveI : IsIso (equalizer.ι f' g').left :=
    (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _)
      (arrowIsoSpecΓOfIsAffine (equalizer.ι f' g').left)).mpr
      (inferInstanceAs (IsIso (Spec.map (equalizer.ι f' g').left.appTop)))
  have h0 : IsIso ((Over.forget Y).map (equalizer.ι f' g')) :=
    (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Y)
  have hfg : f' = g' := (cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g')
  exact congrArg CommaMorphism.left hfg

theorem exists_tangent_dvr_semiabelian {O T K : Type} [CommRing O] [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K] [Algebra T K] [IsFractionRing T K] (a : O →+* T) (G G' : Over (Sp O)) [GrpObj G] [GrpObj G']
    (GK GK' : Over (Sp K)) [GrpObj GK] [GrpObj GK'] (φ : GK.left ⟶ G.left) (φ' : GK'.left ⟶ G'.left)
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (h : IsGrpPullback GK G (spMap ((algebraMap T K).comp a)) φ)
    (h' : IsGrpPullback GK' G' (spMap ((algebraMap T K).comp a)) φ') (q : GK ⟶ GK') [IsMonHom q]
    (x : Sp T ⟶ Sp O) (hx : x = 𝟙 (Sp T) ≫ spMap a)
    (t : epsAt x ⟶ G) (ht : IsTanAt G _ t) (v : epsAt (𝟙 (Sp K)) ⟶ GK)
    (hv : v.left ≫ φ = spMap (dualMap (algebraMap T K)) ≫ t.left) :
    ∃ w : epsAt x ⟶ G', IsTanAt G' _ w ∧
      (v ≫ q).left ≫ φ' = spMap (dualMap (algebraMap T K)) ≫ w.left := by
  subst hx
  let y : Sp T ⟶ Sp O := spMap a
  let g : Sp K ⟶ Sp T := spMap (algebraMap T K)
  have hgy : g ≫ y = spMap ((algebraMap T K).comp a) := by
    simp only [g, y, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let H := (Over.pullback y).obj G
  let H' := (Over.pullback y).obj G'
  have hH : IsGrpPullback H G y (pullback.fst G.hom y) := isGrpPullback_pullback G y
  have hH' : IsGrpPullback H' G' y (pullback.fst G'.hom y) := isGrpPullback_pullback G' y
  have hA := ((isGrpPullback_pullback H g).comp hH).congr hgy rfl
  have hA' := ((isGrpPullback_pullback H' g).comp hH').congr hgy rfl
  obtain ⟨α, hαm, hα⟩ := grpPullback_iso hA h
  obtain ⟨β, hβm, hβ⟩ := grpPullback_iso h' hA'
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian T K H H'
    (IsSemiAbelian.pullback y G hG) (IsSemiAbelian.pullback y G' hG') (α.hom ≫ q ≫ β.hom) inferInstance
  let w₀ : epsAt (𝟙 (Sp T)) ⟶ H := (LiePull.tanPts hH (𝟙 _)).symm t
  have hw₀ : w₀.left ≫ pullback.fst G.hom y = t.left := by
    rw [← LiePull.pts_left hH (LiePull.eps_assoc _) w₀]
    exact congrArg (fun z => z.left) ((LiePull.tanPts hH (𝟙 _)).apply_symm_apply t)
  have hw₀t : IsTanAt H _ w₀ := (LiePull.isTan_iff hH _ w₀).1 (by
    rw [show LiePull.tanPts hH (𝟙 _) w₀ = t from (LiePull.tanPts hH (𝟙 _)).apply_symm_apply t]
    exact ht)
  have hw₁t : IsTanAt H' (𝟙 _) (w₀ ≫ F) := by
    unfold IsTanAt at hw₀t ⊢
    rw [Over.comp_left, ← Category.assoc, hw₀t, ← Over.comp_left, MonObj.one_comp]
  refine ⟨LiePull.tanPts hH' (𝟙 _) (w₀ ≫ F), (LiePull.isTan_iff hH' _ _).2 hw₁t, ?_⟩
  have hpull : ∀ {X Y : Over (Sp T)} (b : X ⟶ Y),
      ((Over.pullback g).map b).left ≫ pullback.fst Y.hom g = pullback.fst X.hom g ≫ b.left :=
    fun b => pullback.lift_fst _ _ _
  have hαi : α.inv.left ≫ pullback.fst H.hom g ≫ pullback.fst G.hom y = φ := by
    rw [← hα, ← Category.assoc, ← Over.comp_left, α.inv_hom_id, Over.id_left, Category.id_comp]
  have hz : v.left ≫ α.inv.left ≫ pullback.fst H.hom g =
      spMap (dualMap (algebraMap T K)) ≫ w₀.left := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hαi, hv, hw₀]
    · have c1 : pullback.fst H.hom g ≫ pullback.snd G.hom y = pullback.snd H.hom g ≫ g :=
        pullback.condition
      have c2 : α.inv.left ≫ pullback.snd H.hom g = GK.hom := Over.w α.inv
      have c3 : v.left ≫ GK.hom = (epsAt (𝟙 (Sp K))).hom := Over.w v
      have c4 : w₀.left ≫ pullback.snd G.hom y = (epsAt (𝟙 (Sp T))).hom := Over.w w₀
      simp only [Category.assoc]
      rw [c1, reassoc_of% c2, reassoc_of% c3, c4]
      have c5 := LieTangent.spec_dual_alg (algebraMap T K)
      show (Spec.map _ ≫ 𝟙 _) ≫ g = spMap _ ≫ Spec.map _ ≫ 𝟙 _
      rw [Category.comp_id, Category.comp_id]
      exact c5.symm
  have hq : q ≫ β.hom = α.inv ≫ (Over.pullback g).map F := by
    rw [hF', Iso.inv_hom_id_assoc]
  have hql : q.left ≫ β.hom.left = α.inv.left ≫ ((Over.pullback g).map F).left := by
    rw [← Over.comp_left, hq, Over.comp_left]
  show (v.left ≫ q.left) ≫ φ' = _ ≫ (w₀.left ≫ F.left) ≫ pullback.fst G'.hom y
  rw [← hβ]
  simp only [Category.assoc]
  rw [reassoc_of% hql, reassoc_of% (hpull F)]
  rw [← Category.assoc (spMap _), ← hz]
  simp only [Category.assoc]

theorem exists_tangent_dvr {O T K : Type} [CommRing O] [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K] [Algebra T K] [IsFractionRing T K] (a : O →+* T) (G G' : Over (Sp O)) [GrpObj G] [GrpObj G']
    (GK GK' : Over (Sp K)) [GrpObj GK] [GrpObj GK'] (φ : GK.left ⟶ G.left) (φ' : GK'.left ⟶ G'.left)
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (h : IsGrpPullback GK G (spMap ((algebraMap T K).comp a)) φ)
    (h' : IsGrpPullback GK' G' (spMap ((algebraMap T K).comp a)) φ') (q : GK ⟶ GK') [IsMonHom q]
    (t : epsAt (spMap a ≫ 𝟙 _) ⟶ G) (ht : IsTanAt G _ t) (v : epsAt (𝟙 (Sp K)) ⟶ GK)
    (hv : v.left ≫ φ = spMap (dualMap (algebraMap T K)) ≫ t.left) :
    ∃ w : epsAt (spMap a ≫ 𝟙 _) ⟶ G', IsTanAt G' _ w ∧
      (v ≫ q).left ≫ φ' = spMap (dualMap (algebraMap T K)) ≫ w.left :=
  exists_tangent_dvr_semiabelian a G G' GK GK' φ φ' hG hG' h h' q _ (by simp) t ht v hv

theorem lifts_id {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] {x : Sp R ⟶ S}
    {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) (c : R →+* R') (e : E)
    (v : epsAt (spMap c ≫ x) ⟶ G) (h : M.Lifts c (𝟙 G.left) e v) :
    v.left = spMap (dualMap c) ≫ (M.pt e).left :=
  (Category.comp_id _).symm.trans h

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (d : A →+* B) (d' : B →+* C) :
    dualMap (d'.comp d) = (dualMap d').comp (dualMap d) := by
  ext x <;> simp [dualMap]

theorem spMap_dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (d : A →+* B) (d' : B →+* C) :
    spMap (dualMap (d'.comp d)) = spMap (dualMap d') ≫ spMap (dualMap d) := by
  rw [dualMap_comp]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_local {O K : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    (G G' : Over (Sp O)) [GrpObj G] [GrpObj G']
    (GK GK' : Over (Sp K)) [GrpObj GK] [GrpObj GK'] (φ : GK.left ⟶ G.left) (φ' : GK'.left ⟶ G'.left)
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (h : IsGrpPullback GK G (spMap (algebraMap O K)) φ)
    (h' : IsGrpPullback GK' G' (spMap (algebraMap O K)) φ') (q : GK ⟶ GK') [IsMonHom q]
    (P : Ideal O) [P.IsMaximal] (c : Localization.AtPrime P →+* K)
    (hc : c.comp (algebraMap O _) = algebraMap O K)
    (t : epsAt (spMap (algebraMap O (Localization.AtPrime P)) ≫ 𝟙 _) ⟶ G)
    (ht : IsTanAt G _ t) (v : epsAt (𝟙 (Sp K)) ⟶ GK)
    (hv : v.left ≫ φ = spMap (dualMap c) ≫ t.left)
    (u : epsAt (spMap (algebraMap O K) ≫ 𝟙 _) ⟶ G') (hu : IsTanAt G' _ u)
    (huv : u.left = (v ≫ q).left ≫ φ') :
    ∃ w : epsAt (spMap (algebraMap O (Localization.AtPrime P)) ≫ 𝟙 _) ⟶ G', IsTanAt G' _ w ∧
      u.left = spMap (dualMap c) ≫ w.left := by
  letI : Algebra (Localization.AtPrime P) K := c.toAlgebra
  have hcK : algebraMap (Localization.AtPrime P) K = c := rfl
  haveI : IsScalarTower O (Localization.AtPrime P) K := IsScalarTower.of_algebraMap_eq' hc.symm
  haveI : IsFractionRing (Localization.AtPrime P) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ K
  by_cases hO : IsField O
  ·
    have hsur : Function.Surjective c := by
      intro z
      obtain ⟨o, ho⟩ := (IsFractionRing.surjective_iff_isField (R := O) (K := K)).2 hO z
      exact ⟨algebraMap O _ o, by rw [← ho, ← hc]; rfl⟩
    have hb : Function.Bijective c := ⟨IsFractionRing.injective (Localization.AtPrime P) K, hsur⟩
    let eqv := RingEquiv.ofBijective c hb
    let c' : K →+* Localization.AtPrime P := eqv.symm.toRingHom
    have h1 : c'.comp c = RingHom.id _ := RingHom.ext fun z => eqv.symm_apply_apply z
    have h2 : c.comp c' = RingHom.id _ := RingHom.ext fun z => eqv.apply_symm_apply z
    have h3 : c'.comp (algebraMap O K) = algebraMap O _ := by
      rw [← hc, ← RingHom.comp_assoc, h1, RingHom.id_comp]
    have hbase : Spec.map (CommRingCat.ofHom c') ≫ (spMap (algebraMap O K) ≫ 𝟙 _) =
        spMap (algebraMap O (Localization.AtPrime P)) ≫ 𝟙 _ := by
      rw [← Category.assoc, LieTangent.spec_comp, h3]
    refine ⟨LieTangent.epsBase c' hbase ≫ u, LieTangent.isTanAt_base c' hbase hu, ?_⟩
    show u.left = spMap (dualMap c) ≫ spMap (dualMap c') ≫ u.left
    have h4 : dualMap (RingHom.id K) = RingHom.id _ := by
      ext x <;> simp [dualMap]
    rw [← Category.assoc, ← spMap_dualMap_comp, h2, h4]
    simp [spMap]
  · have hP : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField ‹_› hO
    haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O hP _
    rw [← hc] at h h'
    obtain ⟨w, hw, hw'⟩ := exists_tangent_dvr (T := Localization.AtPrime P) (K := K)
      (algebraMap O _) G G' GK GK' φ φ' hG hG' h h' q t ht v hv
    exact ⟨w, hw, huv.trans hw'⟩

theorem hom_maps_lie : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (G G' : Over (Sp O)) [GrpObj G] [GrpObj G'] (GK GK' : Over (Sp K)) [GrpObj GK] [GrpObj GK'] (φ : GK.left ⟶ G.left) (φ' : GK'.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap O K)) φ → IsGrpPullback GK' G' (spMap (algebraMap O K)) φ' → ∀ (q : GK ⟶ GK') [IsMonHom q] (E : Type) [AddCommGroup E] [Module O E] (E' : Type) [AddCommGroup E'] [Module O E'] (M : LieModel G (𝟙 _) E) (M' : LieModel G' (𝟙 _) E'), ∃ f : E →ₗ[O] E', ∀ (e : E) (v : epsAt (𝟙 (Sp K)) ⟶ GK), M.Lifts (algebraMap O K) φ e v → M'.Lifts (algebraMap O K) φ' (f e) (v ≫ q) := by
  intro O K _ _ _ _ _ G G' _ _ GK GK' _ _ φ φ' hG hG' h h' q _ E _ _ E' _ _ M M'
  have := hG.comm
  have := hG'.comm
  have := hG'.smooth
  have := hG'.separated
  obtain ⟨EK, i1, i2, MK, N, j, hMK, hj⟩ := exists_generic_model (algebraMap O K) G GK φ h M
  obtain ⟨EK', i1', i2', MK', N', j', hMK', hj'⟩ := exists_generic_model (algebraMap O K) G' GK' φ' h' M'
  obtain ⟨D, hD, -⟩ := lieModel_exists_unique_diff (Sp K) GK GK' K (𝟙 _) EK EK' MK MK' q
  have hc : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hj'' : ∀ a, spMap (dualMap (algebraMap O K)) ≫ (M'.pt a).left = (N'.pt (j' a)).left :=
    fun a => (lifts_id _ _ _ _ (hj' a)).symm
  have hjj : ∀ a, spMap (dualMap (algebraMap O K)) ≫ (M.pt a).left = (N.pt (j a)).left :=
    fun a => (lifts_id _ _ _ _ (hj a)).symm
  have hinj : Function.Injective j' := fun a b hab => M'.inj (Over.OverMorphism.ext
    (ext_of_spMap_injective (dualMap (algebraMap O K)) (LieTangent.dualMap_injective hc) G'.hom _ _
      ((Over.w (M'.pt a)).trans (Over.w (M'.pt b)).symm) (by rw [hj'', hj'', hab])))
  have key : ∀ e, ∃ e', j' e' = D (j e) := by
    intro e
    have hloc : ∀ (P : Ideal O) [P.IsMaximal] (c : Localization.AtPrime P →+* K),
        c.comp (algebraMap O _) = algebraMap O K →
        ∃ w : epsAt (spMap (algebraMap O (Localization.AtPrime P)) ≫ 𝟙 _) ⟶ G', IsTanAt G' _ w ∧
          (N'.pt (D (j e))).left = spMap (dualMap c) ≫ w.left := by
      intro P _ c hcP
      obtain ⟨ET, t1, t2, ⟨L⟩⟩ := lieModel_exists (Sp O) G (Localization.AtPrime P)
        (spMap (algebraMap O (Localization.AtPrime P)) ≫ 𝟙 _)
      obtain ⟨jT, hjT, -⟩ := LieBaseChange.existsUnique_semilinear_lifts (Sp O) G O _
        (algebraMap O (Localization.AtPrime P)) (𝟙 _) E ET M L
      refine exists_local G G' GK GK' φ φ' hG hG' h h' q P c hcP (L.pt (jT e)) (L.tan _) (MK.pt (j e)) ?_
        (N'.pt (D (j e))) (N'.tan _) ?_
      · rw [hMK, ← hjj, lifts_id _ _ _ _ (hjT e), ← Category.assoc, ← spMap_dualMap_comp, hcP]
      · rw [← hD, hMK']
    obtain ⟨e', he'⟩ := GlobalTheory.T.tangent_vector_extends_dvr O K (Sp O) (𝟙 _) G' E' M' (N'.pt (D (j e))) (N'.tan _) hloc
    have he'' := lifts_id _ _ _ _ he'
    rw [hj''] at he''
    exact ⟨e', N'.inj (Over.OverMorphism.ext he'').symm⟩
  choose f hf using key
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, fun e v hv => ?_⟩
  · intro a b
    apply hinj
    simp only [hf, map_add]
  · intro r a
    apply hinj
    simp only [hf, map_smulₛₗ, RingHom.id_apply]
  · have hvj : v = MK.pt (j e) := by
      apply Over.OverMorphism.ext
      apply h.1.hom_ext
      · unfold LieModel.Lifts at hv
        rw [hv, hMK, ← hjj]
      · exact (Over.w v).trans (Over.w (MK.pt (j e))).symm
    have e1 : v ≫ q = MK'.pt (j' (f e)) := by rw [hvj, ← hD, hf]
    show (v ≫ q).left ≫ φ' = spMap (dualMap (algebraMap O K)) ≫ (M'.pt (f e)).left
    rw [e1, hMK', hj'']

end GlobalTheory.CompanionTheory.Ar.LieHomOk
