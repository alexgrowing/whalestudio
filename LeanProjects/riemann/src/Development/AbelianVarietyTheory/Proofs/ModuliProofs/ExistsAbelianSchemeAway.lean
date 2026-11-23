import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpObjOfDenseOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfIsSchemeTheoreticallyDominantOfFractionRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericFlatnessScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothOfRelDimOfIsUnitProperFlat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOpenConditionSmoothProject
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsGenericSpreadOut

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SpreadAb

theorem exists_projModel (R K : Type) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{0}} (p : X ⟶ Sp K) (hp : IsProjOver p) :
    ∃ (Z : Scheme.{0}) (s : Z ⟶ Sp R) (φ : X ⟶ Z), IsProjOver s ∧ IsPullback φ p s (spMap (algebraMap R K)) := by
  obtain ⟨N, i, hi, rfl⟩ := hp
  have P := ProjSpace.isPullback_baseChange N (algebraMap R K)
  set b := ProjSpace.baseChange N (algebraMap R K)
  have hfl : Flat (spMap (algebraMap R K)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors R))
  have hpre : IsPreimmersion (spMap (algebraMap R K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hqb : QuasiCompact b := MorphismProperty.of_isPullback P.flip inferInstance
  let w := i ≫ b
  let s := w.imageι ≫ PSpace.str R N
  have hw : w.toImage ≫ s = (i ≫ PSpace.str K N) ≫ spMap (algebraMap R K) := by
    simp only [s, w, Scheme.Hom.toImage_imageι_assoc, Category.assoc, P.w]
  have hd := isSchemeTheoreticallyDominant_toImage w
  have : QuasiCompact (w.toImage ≫ w.imageι) := by rw [w.toImage_imageι]; infer_instance
  have : QuasiCompact w.toImage := QuasiCompact.of_comp w.toImage w.imageι
  let l : X ⟶ pullback w.imageι b := pullback.lift w.toImage i w.toImage_imageι
  have hl₁ : l ≫ pullback.fst _ _ = w.toImage := pullback.lift_fst _ _ _
  have hl₂ : l ≫ pullback.snd _ _ = i := pullback.lift_snd _ _ _
  have hbf : Flat b := MorphismProperty.of_isPullback P.flip hfl
  have hbm : IsPreimmersion b := MorphismProperty.of_isPullback P.flip hpre
  have : IsClosedImmersion (l ≫ pullback.snd _ _) := by rwa [hl₂]
  have : IsClosedImmersion l := IsClosedImmersion.of_comp l (pullback.snd _ _)
  have Q : IsPullback l (𝟙 X) (pullback.fst w.imageι b) w.toImage :=
    ⟨⟨by rw [hl₁, Category.id_comp]⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => c.snd)
      (fun c => by rw [← cancel_mono (pullback.fst w.imageι b), Category.assoc, hl₁, c.condition])
      (fun c => Category.comp_id _) (fun c m _ h => by rw [← h, Category.comp_id])⟩⟩
  have : IsSchemeTheoreticallyDominant l := .of_isPullback Q.flip
  have : IsIso l := IsClosedImmersion.isIso_iff_ker_eq_bot.2 l.ker_eq_bot
  refine ⟨_, s, w.toImage, ⟨N, w.imageι, inferInstance, rfl⟩, ?_⟩
  have Q₂ := (IsPullback.of_hasPullback w.imageι b).paste_vert P
  refine IsPullback.of_iso Q₂ (asIso l).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [← hl₁]
  · simp [← hl₂]
  · simp [s]
  · simp

theorem iff_iterated (P : MorphismProperty Scheme.{0}) [P.RespectsIso] {R R₁ R₂ : Type} [CommRing R] [CommRing R₁]
    [CommRing R₂] {Z Y : Scheme.{0}} {s : Z ⟶ Sp R} (c : R →+* R₁) (d : R₁ →+* R₂) {e : R →+* R₂}
    (he : d.comp c = e) {a : Y ⟶ Z} {q : Y ⟶ Sp R₂} (h : IsPullback a q s (spMap e)) :
    P q ↔ P (pullback.snd (pullback.snd s (spMap c)) (spMap d)) := by
  subst he
  have h₂ := (IsPullback.of_hasPullback (pullback.snd s (spMap c)) (spMap d)).paste_horiz
    (IsPullback.of_hasPullback s (spMap c))
  have e : spMap d ≫ spMap c = spMap (d.comp c) := by
    rw [← Spec.map_comp]; rfl
  rw [e] at h₂
  rw [← P.cancel_left_of_respectsIso (h.isoIsPullback _ _ h₂).hom, IsPullback.isoIsPullback_hom_snd]

def toFrac (R K : Type) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K] {f : R} (hf : f ≠ 0) :
    Localization.Away f →+* K :=
  IsLocalization.Away.lift f (g := algebraMap R K)
    (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hf))

theorem toFrac_comp (R K : Type) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K] {f : R} (hf : f ≠ 0) :
    (toFrac R K hf).comp (algebraMap R _) = algebraMap R K :=
  IsLocalization.Away.lift_comp _ _

theorem toFrac_injective (R K : Type) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K] {f : R}
    (hf : f ≠ 0) : Function.Injective (toFrac R K hf) := by
  refine (IsLocalization.lift_injective_iff _).2 fun x y => ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg (toFrac R K hf) h
    rwa [← RingHom.comp_apply, ← RingHom.comp_apply, toFrac_comp] at this
  · rw [IsFractionRing.injective R K h]

theorem near_of_away (P : MorphismProperty Scheme.{0}) [P.RespectsIso] (R K : Type) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] {f : R} (hf : f ≠ 0) {Z : Scheme.{0}} (s : Z ⟶ Sp R)
    (h : ∃ f₁ : Localization.Away f, toFrac R K hf f₁ ≠ 0 ∧ ∀ (R' : Type) [CommRing R']
      (φ : Localization.Away f →+* R'), IsUnit (φ f₁) →
        P (pullback.snd (pullback.snd s (spMap (algebraMap R (Localization.Away f)))) (spMap φ))) :
    ∃ f₂ : R, f₂ ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f₂) →
      IsUnit (φ f) ∧ P (pullback.snd s (spMap φ)) := by
  obtain ⟨f₁, h₁, H⟩ := h
  obtain ⟨⟨a, u⟩, hu⟩ := IsLocalization.surj (Submonoid.powers f) f₁
  have hunit := IsLocalization.map_units (Localization.Away f) u
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero, hunit.mul_left_eq_zero] at hu
    exact h₁ (by rw [hu, map_zero])
  refine ⟨f * a, mul_ne_zero hf ha, fun R' _ φ hφ => ?_⟩
  rw [map_mul, IsUnit.mul_iff] at hφ
  refine ⟨hφ.1, ?_⟩
  let d : Localization.Away f →+* R' := IsLocalization.Away.lift f hφ.1
  have hd : d.comp (algebraMap R _) = φ := IsLocalization.Away.lift_comp _ _
  refine (iff_iterated P _ d hd (IsPullback.of_hasPullback _ _)).2 (H R' d ?_)
  have e := congrArg d hu
  rw [map_mul, ← RingHom.comp_apply d (algebraMap R _) a, hd] at e
  exact isUnit_of_mul_isUnit_left (e ▸ hφ.2)

theorem isProper_of_isProjOver {R : Type} [CommRing R] {Z : Scheme.{0}} {s : Z ⟶ Sp R} (hs : IsProjOver s) :
    IsProper s := by
  obtain ⟨N, i, _, rfl⟩ := hs
  have : IsProper (PSpace.str R N) := isProper_str R N
  infer_instance

theorem near_smooth_connected (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {X Z : Scheme.{0}} {p : X ⟶ Sp K} {s : Z ⟶ Sp R} {φ : X ⟶ Z} (hs : IsProjOver s)
    (h : IsPullback φ p s (spMap (algebraMap R K))) (g : ℕ) (hg : SmoothOfRelativeDimension g p)
    (hc : GeometricallyConnected p) :
    ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (c : R →+* R'), IsUnit (c f) →
      SmoothOfRelativeDimension g (pullback.snd s (spMap c)) ∧ GeometricallyConnected (pullback.snd s (spMap c)) := by
  have hpr : IsProper s := isProper_of_isProjOver hs
  have : MorphismProperty.RespectsIso (C := Scheme.{0}) @GeometricallyConnected := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  have : MorphismProperty.RespectsIso (C := Scheme.{0}) (@SmoothOfRelativeDimension g) :=
    @MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _ (smoothOfRelativeDimension_isStableUnderBaseChange g)
  obtain ⟨f₁, hf₁, H₁⟩ := GlobalTheory.generic_flatness_scheme R Z s inferInstance inferInstance
  obtain ⟨f₂, hf₂, H₂⟩ := near_of_away (@SmoothOfRelativeDimension g) R K hf₁ s
    (GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit _ _ _ g K (toFrac R K hf₁) inferInstance (H₁ _ _ (IsLocalization.Away.algebraMap_isUnit f₁))
      ((iff_iterated (@SmoothOfRelativeDimension g) _ _ (toFrac_comp R K hf₁) h).1 hg))
  have hsm := (H₂ (Localization.Away f₂) _ (IsLocalization.Away.algebraMap_isUnit f₂)).2
  obtain ⟨f₃, hf₃, H₃⟩ := near_of_away @GeometricallyConnected R K hf₂ s
    (GlobalTheory.ConnOpen.geometricallyConnected_near _ _ _ K (toFrac R K hf₂) (ProjSpace.isProjOver_pullback_snd _ hs)
      (SmoothOfRelativeDimension.smooth g _)
      ((iff_iterated @GeometricallyConnected _ _ (toFrac_comp R K hf₂) h).1 hc))
  exact ⟨f₃, hf₃, fun R' _ c hc => ⟨(H₂ R' c (H₃ R' c hc).1).2, (H₃ R' c hc).2⟩⟩

theorem near_hom (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {B Z W : Scheme.{0}} (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R) [QuasiCompact pB] [QuasiSeparated pB]
    [LocallyOfFinitePresentation pZ] {φ : W ⟶ B} {p : W ⟶ Sp K} (h : IsPullback φ p pB (spMap (algebraMap R K)))
    (u : W ⟶ Z) (hu : u ≫ pZ = φ ≫ pB) :
    ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (c : R →+* R'), IsUnit (c f) →
      ∀ (Y : Scheme.{0}) (a : Y ⟶ B) (q : Y ⟶ Sp R'), a ≫ pB = q ≫ spMap c →
        ∃ u' : Y ⟶ Z, u' ≫ pZ = a ≫ pB ∧ ∀ j : W ⟶ Y, j ≫ a = φ → j ≫ u' = u := by
  obtain ⟨f, hf, u', H⟩ := GlobalTheory.morphisms_generic_spread_out R K B Z pB pZ Unit (fun _ => h.isoPullback.inv ≫ u) ‹_› ‹_› ‹_›
    (fun _ => by rw [Category.assoc, hu, h.isoPullback_inv_fst_assoc])
  obtain ⟨H₁, H₂⟩ := H ()
  refine ⟨f, hf, fun R' _ c hc Y a q w => ?_⟩
  let d : Localization.Away f →+* R' := IsLocalization.Away.lift f hc
  have hd : d.comp (algebraMap R _) = c := IsLocalization.Away.lift_comp _ _
  let k : Y ⟶ pullback pB (spMap (algebraMap R (Localization.Away f))) := pullback.lift a (q ≫ spMap d) (by
    rw [w, Category.assoc, ← Spec.map_comp, ← hd]; rfl)
  have hk : k ≫ pullback.fst _ _ = a := pullback.lift_fst _ _ _
  refine ⟨k ≫ u' (), by rw [Category.assoc, H₁, reassoc_of% hk], fun j hj => ?_⟩
  have e := H₂ (h.isoPullback.inv ≫ j ≫ k) (by simp only [Category.assoc, hk, hj, h.isoPullback_inv_fst])
  rw [← cancel_epi h.isoPullback.inv, ← e]
  simp only [Category.assoc]

theorem hom_ext_of_points {Z U : Scheme.{0}} (j : U ⟶ Z) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    {X Y : Over Z} [Flat X.hom] [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  refine ExtUnique.over_hom_ext_of_isPullback (IsPullback.of_hasPullback X.hom j) ?_
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom j))
    (Over.homMk (pullback.fst X.hom j) (by simpa using pullback.condition)))

open GrpDense (pushPt_surjective pushPt_mul pushPt_inv pushPt_one) in

theorem grpObj_of_dominant {Z U : Scheme.{0}} (j : U ⟶ Z) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    (G : Over Z) [Flat G.hom] [IsSeparated G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left)
    (h : IsPullback φ A.hom G.hom j) (m : G ⊗ G ⟶ G) (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G)
    (hm : ∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ)
    (hi : φ ≫ i.left = (ι[A]).left ≫ φ) (he : j ≫ e.left = (η[A]).left ≫ φ) :
    ∃ _ : GrpObj G, IsCommMonObj G ∧ IsGrpPullback A G j φ := by
  have := ExtUnique.flat_tensorUnit (S := Z)
  have := ExtUnique.flat_tensorObj G G
  have := ExtUnique.flat_tensorObj (𝟙_ _) G
  have := ExtUnique.flat_tensorObj G (𝟙_ _)
  have := ExtUnique.flat_tensorObj (G ⊗ G) G
  have hM := fun {T : Over U} => pushPt_mul h.w hm (T := T)
  have hI := fun {T : Over U} => pushPt_inv h.w hi (T := T)
  have hE := pushPt_one h.w he
  letI : MonObj G :=
    { one := e
      mul := m
      one_mul := hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (toUnit _) (pushPt h.w x) :=
          CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hx])
        rw [lift_whiskerRight_assoc, hE, hM, _root_.one_mul, lift_leftUnitor_hom]
      mul_one := hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
        obtain rfl : t = lift (pushPt h.w x) (toUnit _) :=
          CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        rw [lift_whiskerLeft_assoc, hE, hM, _root_.mul_one, lift_rightUnitor_hom]
      mul_assoc := hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (lift (pushPt h.w x) (pushPt h.w y)) (pushPt h.w z) := by
          ext <;> simp [hx, hy, hz]
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hM, hM, hM, hM,
          _root_.mul_assoc] }
  letI : GrpObj G :=
    { inv := i
      left_inv := hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, inv_mul_cancel, comp_toUnit_assoc, hE]
      right_inv := hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, mul_inv_cancel, comp_toUnit_assoc, hE] }
  refine ⟨inferInstance, ⟨hom_ext_of_points j fun T t => ?_⟩, h, fun T x y x₀ y₀ hx hy => ?_⟩
  · obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ snd _ _)
    obtain rfl : t = lift (pushPt h.w x) (pushPt h.w y) := by ext <;> simp [hx, hy]
    change _ ≫ _ ≫ m = _ ≫ m
    rw [lift_braiding_hom_assoc, hM, hM, _root_.mul_comm]
  · obtain rfl : x₀ = pushPt h.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = pushPt h.w y := Over.OverMorphism.ext hy
    exact congrArg (fun z => z.left) (hM x y)

theorem isPullback_square {S U Z X : Scheme.{0}} {s : Z ⟶ S} {j : U ⟶ S} {p : X ⟶ U} {φ : X ⟶ Z}
    (h : IsPullback φ p s j) :
    IsPullback (pullback.map p p s s φ φ j h.w.symm h.w.symm) (pullback.fst p p ≫ p) (pullback.fst s s ≫ s) j := by
  have h₁ : IsPullback (pullback.map p p s s φ φ j h.w.symm h.w.symm) (pullback.fst p p) (pullback.fst s s) φ := by
    refine IsPullback.of_right (h₁₂ := pullback.snd s s) (v₁₃ := s) (h₂₂ := s) ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback s s).flip
    rw [pullback.lift_snd, h.w]
    exact (IsPullback.of_hasPullback p p).flip.paste_horiz h
  exact h₁.paste_vert h

theorem exists_abelianScheme_away : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp K)), ∃ (f : R) (_ : f ≠ 0) (ψ : (Localization.Away f) →+* K) (A : Over (Sp (Localization.Away f))) (_ : GrpObj A) (φ : P.A.left ⟶ A.left), ψ.comp (algebraMap R _) = algebraMap R K ∧ IsAbelianScheme A ∧ SmoothOfRelativeDimension P.g A.hom ∧ IsGrpPullback P.A A (spMap ψ) φ := by
  intro R K _ _ _ _ _ _ P
  obtain ⟨Z, s, φ, hs, h⟩ := exists_projModel R K P.A.hom (ProjSpace.isProjOver_polAV P)
  have hpr : IsProper s := isProper_of_isProjOver hs
  have hfp : LocallyOfFinitePresentation s := inferInstance
  obtain ⟨f₀, hf₀, H₀⟩ := near_smooth_connected R K hs h P.g P.smoothDim P.isAb.geomConnected
  obtain ⟨f₁, hf₁, H₁⟩ := near_hom R K (pullback.fst s s ≫ s) s (isPullback_square h) ((μ[P.A]).left ≫ φ) (by
    rw [(isPullback_square h).w, Category.assoc, h.w, Over.w_assoc]
    rfl)
  obtain ⟨f₂, hf₂, H₂⟩ := near_hom R K s s h ((ι[P.A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc])
  obtain ⟨f₃, hf₃, H₃⟩ := near_hom R K (𝟙 _) s (IsPullback.id_vert (spMap (algebraMap R K)))
    ((η[P.A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc]; simp)
  have hf : f₀ * f₁ * f₂ * f₃ ≠ 0 := by simp [hf₀, hf₁, hf₂, hf₃]
  let R' := Localization.Away (f₀ * f₁ * f₂ * f₃)
  let c := algebraMap R R'
  have hu : IsUnit (c (f₀ * f₁ * f₂ * f₃)) := IsLocalization.Away.algebraMap_isUnit _
  simp only [map_mul, IsUnit.mul_iff] at hu
  obtain ⟨⟨⟨u₀, u₁⟩, u₂⟩, u₃⟩ := hu
  let ψ := toFrac R K hf
  have hψ : spMap ψ ≫ spMap c = spMap (algebraMap R K) := by
    rw [← Spec.map_comp, ← toFrac_comp R K hf]; rfl
  let G : Over (Sp R') := Over.mk (pullback.snd s (spMap c))
  let a : G.left ⟶ Z := pullback.fst s (spMap c)
  have hG : IsPullback a G.hom s (spMap c) := IsPullback.of_hasPullback _ _
  let φ' : P.A.left ⟶ G.left := hG.lift φ (P.A.hom ≫ spMap ψ) (by rw [h.w, Category.assoc, hψ])
  have hφ₁ : φ' ≫ a = φ := hG.lift_fst _ _ _
  have hφ₂ : φ' ≫ G.hom = P.A.hom ≫ spMap ψ := hG.lift_snd _ _ _
  have hφ : IsPullback φ' P.A.hom G.hom (spMap ψ) := IsPullback.of_right (by rwa [hφ₁, hψ]) hφ₂ hG
  obtain ⟨hsm, hgc⟩ := H₀ R' c u₀
  have hsm' : Smooth G.hom := SmoothOfRelativeDimension.smooth P.g (pullback.snd s (spMap c))
  have hpr' : IsProper G.hom := inferInstanceAs (IsProper (pullback.snd s (spMap c)))
  obtain ⟨m, hm₁, hm₂⟩ := H₁ R' c u₁ _ _ _ (isPullback_square hG).w
  obtain ⟨i, hi₁, hi₂⟩ := H₂ R' c u₂ _ _ _ hG.w
  obtain ⟨e, he₁, he₂⟩ := H₃ R' c u₃ _ (spMap c) (𝟙 _) (by simp)
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom ψ) (toFrac_injective R K hf)
  have := P.isAb.comm
  have L : ∀ (Y : Over (Sp R')) (u : Y.left ⟶ Z), u ≫ s = Y.hom ≫ spMap c → ∃ v : Y ⟶ G, v.left ≫ a = u :=
    fun Y u w => ⟨Over.homMk (hG.lift u Y.hom w) (hG.lift_snd _ _ _), hG.lift_fst _ _ _⟩
  obtain ⟨m', hm'⟩ := L (G ⊗ G) m (hm₁.trans (isPullback_square hG).w)
  obtain ⟨i', hi'⟩ := L G i (hi₁.trans hG.w)
  obtain ⟨e', he'⟩ := L (𝟙_ _) e (he₁.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  obtain ⟨_, hc, hp⟩ := grpObj_of_dominant (spMap ψ) G P.A φ' hφ m' i' e'
    (fun φ₂ ⟨k₁, k₂⟩ => by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, hm']
        refine hm₂ φ₂ (pullback.hom_ext ?_ ?_)
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← hφ₁]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ a) k₁).trans (Category.assoc _ _ _))
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← hφ₁]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ a) k₂).trans (Category.assoc _ _ _))
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc, ← Over.w (fst G G), reassoc_of% k₁, hφ₂,
          Over.w_assoc])
    (by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, hi']
        exact hi₂ φ' hφ₁
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc])
    (by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, he']
        exact he₂ _ hψ
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc]
        exact (Category.comp_id _).trans (Category.id_comp _).symm)
  exact ⟨_, hf, ψ, G, inferInstance, φ', toFrac_comp R K hf, ⟨hc, hsm', hpr', hgc⟩, hsm, hp⟩

end GlobalTheory.SpreadAb
