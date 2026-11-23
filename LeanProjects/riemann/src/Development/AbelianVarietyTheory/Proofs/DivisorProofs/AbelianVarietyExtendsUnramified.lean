import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfIsSchemeTheoreticallyDominantOfFractionRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnramifiedClosure

theorem injective_of_map_maximalIdeal {R W : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra R W]
    (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    Function.Injective (algebraMap R W) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hp : (RingHom.ker (algebraMap R W)).IsPrime := RingHom.ker_isPrime _
  have hm : RingHom.ker (algebraMap R W) = maximalIdeal R := IsLocalRing.eq_maximalIdeal (hp.isMaximal hne)
  apply IsDiscreteValuationRing.not_a_field W
  rw [← h, ← hm]
  exact (Ideal.map_eq_bot_iff_le_ker _).2 le_rfl

variable (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K']
  [IsScalarTower R W K'] [IsScalarTower R K K']

theorem isLocalization (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    IsLocalization (Algebra.algebraMapSubmonoid W (nonZeroDivisors R)) K' := by
  have hinj := injective_of_map_maximalIdeal h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖW : Irreducible (algebraMap R W ϖ) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← h,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton]
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, r, hr, rfl⟩
    refine IsUnit.mk0 _ ?_
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact fun h0 => nonZeroDivisors.ne_zero hr (hinj (by rw [map_zero]; exact h0))
  · intro z
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := W) z
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖW
    refine ⟨⟨x * ↑u⁻¹, ⟨algebraMap R W (ϖ ^ n), ϖ ^ n,
      mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hϖ.ne_zero), rfl⟩⟩, ?_⟩
    have hu : algebraMap W K' ↑u * algebraMap W K' ↑u⁻¹ = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hp : algebraMap W K' (algebraMap R W ϖ) ≠ 0 := by
      rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact hϖW.ne_zero
    have hu0 : algebraMap W K' ↑u ≠ 0 := by
      rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact u.ne_zero
    simp only [map_pow, map_mul]
    field_simp
    linear_combination (-(algebraMap W K' x)) * hu
  · intro x y hxy
    exact ⟨1, by simpa using IsFractionRing.injective W K' hxy⟩

theorem isPushout (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    Algebra.IsPushout R K W K' := by
  haveI := isLocalization R W K' h
  constructor
  exact (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K _).1
    (isLocalizedModule_iff_isLocalization.2 this)

theorem isPullback_spec (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    IsPullback (spMap (algebraMap K K')) (spMap (algebraMap W K')) (spMap (algebraMap R K))
      (spMap (algebraMap R W)) := by
  haveI := isPushout R K W K' h
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout R K W K')

theorem flat_spec (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    Flat (spMap (algebraMap R W)) := by
  have hinj := injective_of_map_maximalIdeal h
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  refine GlobalTheory.ringHom_flat_of_injective_of_isUnit (algebraMap R W) (algebraMap W (FractionRing W))
    (IsFractionRing.injective W (FractionRing W)) fun t ht => IsUnit.mk0 _ ?_
  rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
  exact fun h0 => ht (hinj (by rw [h0, map_zero]))

end GlobalTheory.UnramifiedClosure

namespace GlobalTheory.UnramifiedClosure

theorem schDom_spMap {A B : Type} [CommRing A] [CommRing B] [IsReduced A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (spMap φ) := by
  haveI : IsDominant (spMap φ) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

end GlobalTheory.UnramifiedClosure

open GlobalTheory.UnramifiedClosure in
theorem GlobalTheory.UnramifiedClosure.closure_baseChange : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ (P : Over (Sp R)), QuasiSeparated P.hom → ∀ (A : Over (Sp K)), QuasiCompact A.hom → ∀ (G : Over (Sp W)), QuasiCompact G.hom → Flat G.hom → ∀ (e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A) (iA : A.left ⟶ P.left) (hA : iA ≫ P.hom = A.hom ≫ spMap (algebraMap R K)), IsClosedImmersion (pullback.lift iA A.hom hA) → ∀ (iG : G.left ⟶ P.left) (hG : iG ≫ P.hom = G.hom ≫ spMap (algebraMap R W)), IsClosedImmersion (pullback.lift iG G.hom hG) → e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ iA = pullback.fst G.hom (spMap (algebraMap W K')) ≫ iG → ∃ (X : Over (Sp R)) (a : A.left ⟶ X.left) (g : G.left ⟶ X.left), IsPullback a A.hom X.hom (spMap (algebraMap R K)) ∧ IsPullback g G.hom X.hom (spMap (algebraMap R W)) ∧ e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ a = pullback.fst G.hom (spMap (algebraMap W K')) ≫ g := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm P hP A hAq G hGq hGf e iA hA hcA iG hG hcG hcomp

  have hjp : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hjf : Flat (spMap (algebraMap R K)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have hjW : Flat (spMap (algebraMap R W)) := flat_spec R W hm
  have hsq := isPullback_spec R K W K' hm
  have hqc : QuasiCompact iA := by
    have : QuasiCompact (iA ≫ P.hom) := by rw [hA]; infer_instance
    exact QuasiCompact.of_comp iA P.hom
  have hdom : IsSchemeTheoreticallyDominant iA.toImage := GlobalTheory.isSchemeTheoreticallyDominant_toImage iA
  let X : Over (Sp R) := Over.mk (iA.imageι ≫ P.hom)
  have hXh : X.hom = iA.imageι ≫ P.hom := rfl
  have hXa : iA.toImage ≫ X.hom = A.hom ≫ spMap (algebraMap R K) := by
    rw [hXh, Scheme.Hom.toImage_imageι_assoc, hA]
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{0} :=
    ⟨fun f g hf hg ↦ @IsClosedImmersion.comp _ _ _ f g hf hg⟩

  let t : A.left ⟶ pullback X.hom (spMap (algebraMap R K)) := pullback.lift iA.toImage A.hom hXa
  let mK : pullback X.hom (spMap (algebraMap R K)) ⟶ pullback P.hom (spMap (algebraMap R K)) :=
    pullback.map _ _ _ _ iA.imageι (𝟙 _) (𝟙 _) (Category.comp_id _) (by simp)
  have hmK : IsClosedImmersion mK :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{0}) inferInstance inferInstance rfl (by simp)
  have htm : t ≫ mK = pullback.lift iA A.hom hA := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst,
        Scheme.Hom.toImage_imageι]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd,
        Category.comp_id]
  have : IsClosedImmersion (t ≫ mK) := htm ▸ hcA
  have ht : IsClosedImmersion t := IsClosedImmersion.of_comp_isClosedImmersion t mK
  have hpb : IsPullback (𝟙 A.left) t iA.toImage (pullback.fst X.hom (spMap (algebraMap R K))) :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, pullback.lift_fst]⟩
  have htd : IsSchemeTheoreticallyDominant t := .of_isPullback hpb
  have : IsIso t := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr t.ker_eq_bot
  have hIa : IsPullback iA.toImage A.hom X.hom (spMap (algebraMap R K)) :=
    IsPullback.of_iso_pullback ⟨hXa⟩ (asIso t) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

  have hAK : IsPullback (pullback.fst A.hom (spMap (algebraMap K K')))
      (pullback.snd A.hom (spMap (algebraMap K K')) ≫ spMap (algebraMap W K'))
      (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W)) :=
    (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))).paste_vert hsq
  let mW : pullback X.hom (spMap (algebraMap R W)) ⟶ pullback P.hom (spMap (algebraMap R W)) :=
    pullback.map _ _ _ _ iA.imageι (𝟙 _) (𝟙 _) (Category.comp_id _) (by simp)
  have hmW : IsClosedImmersion mW :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{0}) inferInstance inferInstance rfl (by simp)
  let n : pullback (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W)) ⟶
      pullback X.hom (spMap (algebraMap R W)) :=
    pullback.map _ _ _ _ iA.toImage (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hXa]) (by simp)
  have hL : IsPullback (pullback.fst (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W))) n
      iA.toImage (pullback.fst X.hom (spMap (algebraMap R W))) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback X.hom (spMap (algebraMap R W)))
    have h1 : n ≫ pullback.snd X.hom (spMap (algebraMap R W)) =
        pullback.snd (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W)) := by
      rw [pullback.lift_snd, Category.comp_id]
    rw [h1, hXa]
    exact IsPullback.of_hasPullback _ _
  have hn : IsSchemeTheoreticallyDominant n := .of_isPullback hL
  have hsd : IsSchemeTheoreticallyDominant (spMap (algebraMap W K')) :=
    schDom_spMap _ (IsFractionRing.injective W K')
  have hu : IsSchemeTheoreticallyDominant (pullback.fst G.hom (spMap (algebraMap W K'))) :=
    inferInstance
  have he : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let v : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback X.hom (spMap (algebraMap R W)) :=
    e.hom.left ≫ hAK.isoPullback.hom ≫ n
  have hv : IsSchemeTheoreticallyDominant v := inferInstance
  let cG : G.left ⟶ pullback P.hom (spMap (algebraMap R W)) := pullback.lift iG G.hom hG
  have hes : e.hom.left ≫ pullback.snd A.hom (spMap (algebraMap K K')) =
      pullback.snd G.hom (spMap (algebraMap W K')) := Over.w e.hom
  have hcomm : pullback.fst G.hom (spMap (algebraMap W K')) ≫ cG = v ≫ mW := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← hcomp]
      simp only [v, mW, n, Category.assoc]
      rw [pullback.lift_fst]
      try simp only [Category.assoc]
      rw [pullback.lift_fst_assoc]
      try simp only [Category.assoc]
      rw [IsPullback.isoPullback_hom_fst_assoc, Scheme.Hom.toImage_imageι]
    · rw [Category.assoc, pullback.lift_snd]
      simp only [v, mW, n, Category.assoc]
      rw [pullback.lift_snd, Category.comp_id (pullback.snd X.hom (spMap (algebraMap R W))),
        pullback.lift_snd,
        Category.comp_id (pullback.snd (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W))),
        IsPullback.isoPullback_hom_snd, reassoc_of% hes]
      exact pullback.condition
  have hker : mW.ker = cG.ker := by
    have h1 : (pullback.fst G.hom (spMap (algebraMap W K')) ≫ cG).ker = cG.ker := by
      rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    have h2 : (v ≫ mW).ker = mW.ker := by
      rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [← h1, ← h2, hcomm]
  let ψ : G.left ⟶ pullback X.hom (spMap (algebraMap R W)) := IsClosedImmersion.lift mW cG hker.le
  have hψ : ψ ≫ mW = cG := IsClosedImmersion.lift_fac _ _ _
  have : IsIso ψ := IsClosedImmersion.isIso_lift mW cG hker
  have hψs : ψ ≫ pullback.snd X.hom (spMap (algebraMap R W)) = G.hom := by
    have h := congrArg (· ≫ pullback.snd P.hom (spMap (algebraMap R W))) hψ
    simp only [Category.assoc] at h
    rwa [pullback.lift_snd, Category.comp_id, pullback.lift_snd] at h
  have hIg : IsPullback (ψ ≫ pullback.fst X.hom (spMap (algebraMap R W))) G.hom X.hom
      (spMap (algebraMap R W)) :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, reassoc_of% hψs]⟩
      (asIso ψ) rfl hψs
  refine ⟨X, iA.toImage, ψ ≫ pullback.fst X.hom (spMap (algebraMap R W)), hIa, hIg, ?_⟩
  rw [← cancel_mono iA.imageι]
  have h3 : pullback.fst X.hom (spMap (algebraMap R W)) ≫ iA.imageι =
      mW ≫ pullback.fst P.hom (spMap (algebraMap R W)) := (pullback.lift_fst _ _ _).symm
  simp only [Category.assoc]
  rw [Scheme.Hom.toImage_imageι, h3, reassoc_of% hψ, pullback.lift_fst, hcomp]
