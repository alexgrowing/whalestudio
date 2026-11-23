import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.SectionTranslation
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem ext_of_schDom {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (i : W ⟶ X) [IsSchemeTheoreticallyDominant i] (hU : i ≫ f = i ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  haveI : IsSeparated Y'.hom := ‹IsSeparated s›
  let U' : Over Z := Over.mk (i ≫ f ≫ s)
  let i' : U' ⟶ X' := Over.homMk i
  have e : i' ≫ f' = i' ≫ g' := by
    ext1
    exact hU
  let l := equalizer.lift i' e
  have hi : i = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [← hi]; exact i.ker_eq_bot
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  have h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g')) := (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Z)
  have hfg : f' = g' := (cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g')
  exact congrArg CommaMorphism.left hfg

theorem schDom_spec_map {A B : Type} [CommRing A] [CommRing B] [IsReduced A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

theorem j_isPullback (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  have h := Over.w M.e.inv
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  refine IsPullback.of_iso (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))
    (asIso M.e.inv.left).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [Model.j]
  · simp [← h]

theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j := by
  have h1 : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y) = fst A A' ≫ M.e.inv := by
    simp [Model.prod]
  have h2 := congrArg (fun q => q.left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))) h1
  have h3 : ((Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y)).left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))
      = pullback.fst (M.Y ⊗ N.Y).hom (spMap (algebraMap R K)) ≫ (fst M.Y N.Y).left := pullback.lift_fst _ _ _
  refine (Category.assoc _ _ _).trans ((congrArg ((M.prod N).e.inv.left ≫ ·) h3.symm).trans ?_)
  exact (Category.assoc _ _ _).symm.trans (h2.trans (Category.assoc _ _ _))

theorem prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j := by
  have h1 : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (snd M.Y N.Y) = snd A A' ≫ N.e.inv := by
    simp [Model.prod]
  have h2 := congrArg (fun q => q.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h1
  have h3 : ((Over.pullback (spMap (algebraMap R K))).map (snd M.Y N.Y)).left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))
      = pullback.fst (M.Y ⊗ N.Y).hom (spMap (algebraMap R K)) ≫ (snd M.Y N.Y).left := pullback.lift_fst _ _ _
  refine (Category.assoc _ _ _).trans ((congrArg ((M.prod N).e.inv.left ≫ ·) h3.symm).trans ?_)
  exact (Category.assoc _ _ _).symm.trans (h2.trans (Category.assoc _ _ _))

theorem extends_apply {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens}
    {g : U.toScheme ⟶ N.Y.left} (h : Extends M N f U g) {T : Scheme.{0}} (t : T ⟶ A.left) (u : T ⟶ U.toScheme)
    (e : u ≫ U.ι = t ≫ M.j) : u ≫ g = t ≫ f.left ≫ N.j := by
  have hp := isPullback_morphismRestrict M.j U
  rw [← hp.lift_fst u t e, Category.assoc, h.2, ← Category.assoc, hp.lift_snd]

theorem ext_generic [IsDomain R] [IsFractionRing R K] (M : Model R A) (U : M.Y.left.Opens) {Y Z : Scheme.{0}}
    {f g : U.toScheme ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (hU : (M.j ∣_ U) ≫ f = (M.j ∣_ U) ≫ g) : f = g := by
  have := M.smooth
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) := schDom_spec_map _ (IsFractionRing.injective R K)
  have hp := (isPullback_morphismRestrict M.j U).paste_vert (j_isPullback M)
  have : IsSchemeTheoreticallyDominant (M.j ∣_ U) := IsSchemeTheoreticallyDominant.of_isPullback hp.flip
  exact ext_of_schDom s h _ hU

theorem slice_isPullback {S : Scheme.{0}} (Y : Over S) (s : 𝟙_ (Over S) ⟶ Y) :
    IsPullback (lift (toUnit Y ≫ s) (𝟙 Y)).left Y.hom (fst Y Y).left s.left := by
  have hs : s.left ≫ Y.hom = 𝟙 S := Over.w s
  have h1 : (lift (toUnit Y ≫ s) (𝟙 Y)).left ≫ (snd Y Y).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have h2 : (lift (toUnit Y ≫ s) (𝟙 Y)).left ≫ (fst Y Y).left = Y.hom ≫ s.left := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h3 : IsPullback (snd Y Y).left (fst Y Y).left Y.hom Y.hom := (IsPullback.of_hasPullback Y.hom Y.hom).flip
  refine IsPullback.of_right ?_ h2 h3
  rw [h1, hs]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

theorem isoAt_slice [IsDomain R] [IsFractionRing R K] (M : Model R A) (s : 𝟙_ (Over (Sp R)) ⟶ M.Y)
    (a : 𝟙_ (Over (Sp K)) ⟶ A) (ha : a.left ≫ M.j = spMap (algebraMap R K) ≫ s.left)
    (f : A ⊗ A ⟶ A ⊗ A) (hf : f ≫ fst A A = fst A A) (y : M.Y.left)
    (h : IsoAt (M.prod M) (M.prod M) f ((lift (toUnit M.Y ≫ s) (𝟙 M.Y)).left y)) :
    IsoAt M M (lift (toUnit A ≫ a) (𝟙 A) ≫ f ≫ snd A A) y := by
  obtain ⟨U, g, hy, he, hg⟩ := h
  have hsl := slice_isPullback M.Y s
  have h1 : (lift (toUnit M.Y ≫ s) (𝟙 M.Y)).left ≫ (snd M.Y M.Y).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨i, hi⟩ : ∃ i : M.Y.left ⟶ (M.prod M).Y.left, i = (lift (toUnit M.Y ≫ s) (𝟙 M.Y)).left := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : (M.prod M).Y.left ⟶ M.Y.left, p = (fst M.Y M.Y).left := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ p : (M.prod M).Y.left ⟶ M.Y.left, p = (snd M.Y M.Y).left := ⟨_, rfl⟩
  let a' : Sp K ⟶ A.left := a.left
  let s' : Sp R ⟶ M.Y.left := s.left
  replace ha : a' ≫ M.j = spMap (algebraMap R K) ≫ s' := ha
  have hy : i y ∈ U := hi ▸ hy
  replace hsl : IsPullback i M.Y.hom p s' := by subst hi hp; exact hsl
  replace h1 : i ≫ q = 𝟙 _ := by subst hi hq; exact h1
  have hjp : (M.prod M).j ≫ p = (fst A A).left ≫ M.j := by subst hp; exact prod_j_fst M M
  have hjq : (M.prod M).j ≫ q = (snd A A).left ≫ M.j := by subst hq; exact prod_j_snd M M
  have h3 : IsPullback p q M.Y.hom M.Y.hom := by subst hp hq; exact IsPullback.of_hasPullback _ _
  have hph : p ≫ M.Y.hom = (M.prod M).Y.hom := by subst hp; rfl
  have hqh : q ≫ M.Y.hom = (M.prod M).Y.hom := by rw [← h3.w, hph]
  have hih : i ≫ (M.prod M).Y.hom = M.Y.hom := by rw [← hqh, ← Category.assoc, h1, Category.id_comp]
  clear hi hp hq
  have hj : (lift (toUnit A ≫ a) (𝟙 A)).left ≫ (M.prod M).j = M.j ≫ i := by
    refine h3.hom_ext ?_ ?_
    · have e1 : (lift (toUnit A ≫ a) (𝟙 A)).left ≫ (fst A A).left = A.hom ≫ a' := (slice_isPullback A a).w
      rw [Category.assoc, Category.assoc, hsl.w, ← Category.assoc M.j, M.j_hom, Category.assoc, ← ha, hjp,
        ← Category.assoc, e1, Category.assoc]
    · have e1 : (lift (toUnit A ≫ a) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ := by
        rw [← Over.comp_left, lift_snd]; rfl
      rw [Category.assoc, Category.assoc, h1, hjq, ← Category.assoc, e1]; simp
  have := M.sep
  have hgp : g ≫ p = U.ι ≫ p := by
    refine ext_generic (M.prod M) U M.Y.hom ?_ ?_
    · rw [Category.assoc, Category.assoc, hph, he.1]
    · rw [← Category.assoc, he.2, ← Category.assoc (_ ∣_ _), morphismRestrict_ι, Category.assoc, Category.assoc,
        Category.assoc, hjp, ← Category.assoc f.left, ← Over.comp_left, hf]
  have hV := isPullback_morphismRestrict i U
  have hg1 : ((i ∣_ U) ≫ g ≫ q) ≫ M.Y.hom = (i ⁻¹ᵁ U).ι ≫ M.Y.hom := by
    rw [Category.assoc, Category.assoc, hqh, he.1, ← Category.assoc, morphismRestrict_ι, Category.assoc, hih]
  have hg2 : ((i ∣_ U) ≫ g ≫ q) ≫ i = (i ∣_ U) ≫ g := by
    refine h3.hom_ext ?_ ?_
    · rw [Category.assoc _ i, hsl.w, ← Category.assoc, hg1, Category.assoc, Category.assoc, hgp, ← hsl.w,
        ← Category.assoc, ← Category.assoc, morphismRestrict_ι]
    · rw [Category.assoc _ i, h1]; simp
  have hpb : IsPullback ((i ∣_ U) ≫ g ≫ q) (i ∣_ U) i g := by
    refine IsPullback.of_right ?_ hg2 hsl.flip
    rw [hg1, hgp]
    exact hV.flip.paste_horiz hsl.flip
  refine ⟨i ⁻¹ᵁ U, (i ∣_ U) ≫ g ≫ q, hy, ⟨hg1, ?_⟩, MorphismProperty.of_isPullback hpb.flip hg⟩
  have e := extends_apply he ((M.j ⁻¹ᵁ (i ⁻¹ᵁ U)).ι ≫ (lift (toUnit A ≫ a) (𝟙 A)).left)
    ((M.j ∣_ (i ⁻¹ᵁ U)) ≫ (i ∣_ U)) (by
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc, hj])
  rw [← Category.assoc, ← Category.assoc, e]
  simp only [Category.assoc, hjq, Over.comp_left]

theorem slice_shear [GrpObj A] [IsCommMonObj A] (a : 𝟙_ (Over (Sp K)) ⟶ A) (b : Bool) :
    lift (toUnit A ≫ a) (𝟙 A) ≫ shear A b ≫ snd A A = if b then (transl a).hom else (transl a).inv := by
  cases b <;> simp [shear, transl, MonObj.comp_mul, GrpObj.comp_inv]

theorem shear_fst [GrpObj A] (b : Bool) : shear A b ≫ fst A A = fst A A := by
  cases b <;> simp [shear]

theorem translation_by_section : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∀ (s : 𝟙_ (Over (Sp R)) ⟶ M.Y), ∃ a : (𝟙_ (Over (Sp K)) ⟶ A), a.left ≫ M.j = spMap (algebraMap R K) ≫ s.left ∧ GenIso M M (transl a).hom ∧ ∀ (y : M.Y.left) (b : Bool), IsoAt (M.prod M) (M.prod M) (shear A b) ((lift (toUnit M.Y ≫ s) (𝟙 M.Y)).left y) → IsoAt M M (if b then (transl a).hom else (transl a).inv) y := by
  intro R K _ _ _ _ _ hSH A _ _ _ M hM s
  have := hSH.2.2.2
  have hs : s.left ≫ M.Y.hom = 𝟙 (Sp R) := Over.w s
  have w : (spMap (algebraMap R K) ≫ s.left) ≫ M.Y.hom = 𝟙 (Sp K) ≫ spMap (algebraMap R K) := by
    rw [Category.assoc, hs]; simp
  let a : 𝟙_ (Over (Sp K)) ⟶ A := Over.homMk ((j_isPullback M).lift _ _ w) ((j_isPullback M).lift_snd _ _ w)
  have ha : a.left ≫ M.j = spMap (algebraMap R K) ≫ s.left := (j_isPullback M).lift_fst _ _ w
  have key : ∀ (y : M.Y.left) (b : Bool), IsoAt (M.prod M) (M.prod M) (shear A b)
      ((lift (toUnit M.Y ≫ s) (𝟙 M.Y)).left y) → IsoAt M M (if b then (transl a).hom else (transl a).inv) y := by
    intro y b h
    rw [← slice_shear]
    exact isoAt_slice M s a ha _ (shear_fst b) y h
  refine ⟨a, ha, ?_, key⟩
  have hx : s.left (IsLocalRing.closedPoint R) ∈ M.sp :=
    congrArg (fun q : Sp R ⟶ Sp R => q (IsLocalRing.closedPoint R)) hs
  obtain ⟨z, hz, hi⟩ := (hM.2 true _ hx).1
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback (slice_isPullback M.Y s) z _ hz
  exact ⟨y, hy, key y true hi⟩

end GlobalTheory.SS.SectionTranslation
end
