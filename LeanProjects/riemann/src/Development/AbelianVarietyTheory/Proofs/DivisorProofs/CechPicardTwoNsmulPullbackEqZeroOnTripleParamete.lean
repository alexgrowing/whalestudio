import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassEqZeroOfZeroDenseOpenAndSectionOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwicePicardClassEqZeroOfTranslatesMemOpenStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pull_two_nsmul_eq_zero_of_triples : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V W : A.left.Opens) (hV : V ≤ W), (U : Set S).Nonempty → (∀ s : S, ∃ x ∈ V, A.hom x = s) → A.hom ⁻¹ᵁ U ≤ W → W ≤ A.hom ⁻¹ᵁ U ⊔ V → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE hV) c = 0 → ∀ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), p ≫ V.ι = v.left → (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) → Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) → GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) → e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ → GlobalTheory.CechPic.pull (x.left ∣_ W) (2 • c) = 0 := by
  intro S _ _ hS A _ hA U V W hV hU hsurj hUW hWUV c hc Y x a v p e hpv hmem hsm hgi he
  have := hA.smooth
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth
      hA.geomConnected
  have : GlobalTheory.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff S).mpr hS
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨s0, hs0⟩ := hU
  obtain ⟨a0, ha0V, ha0⟩ := hsurj s0
  have : Nonempty V := ⟨⟨a0, ha0V⟩⟩
  have : IsIntegral V.toScheme := inferInstance
  have hVn : GlobalTheory.IsNormalScheme V.toScheme := GlobalTheory.isNormalScheme_of_smooth (V.ι ≫ A.hom)
  let i0 := (x.left ⁻¹ᵁ W).ι
  let O : (x.left ⁻¹ᵁ W).toScheme.Opens := i0 ⁻¹ᵁ (x.left ⁻¹ᵁ V)
  have hrange : Set.range (x.left ⁻¹ᵁ V).ι = Set.range (O.ι ≫ i0) := by
    have hO : (O : Set _) = i0 ⁻¹' (x.left ⁻¹ᵁ V : Set Y.left) := rfl
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι, hO, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    ext z
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Scheme.Hom.mem_preimage]
    exact ⟨fun h => ⟨h, hV h⟩, fun h => h.1⟩
  let φ := IsOpenImmersion.isoOfRangeEq (x.left ⁻¹ᵁ V).ι (O.ι ≫ i0) hrange
  have hφ : φ.hom ≫ O.ι ≫ i0 = (x.left ⁻¹ᵁ V).ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let UT : V.toScheme.Opens := (V.ι ≫ A.hom) ⁻¹ᵁ U
  have hUT : (UT : Set V.toScheme).Nonempty := ⟨⟨a0, ha0V⟩, by
    show A.hom (V.ι ⟨a0, ha0V⟩) ∈ U
    simpa [ha0] using hs0⟩
  let p' := i0 ≫ p
  have hOp : O.ι ≫ p' = φ.inv ≫ (x.left ⁻¹ᵁ V).ι ≫ p := by
    rw [← hφ]; simp [p']
  have hsm' : Smooth (O.ι ≫ p') := by rw [hOp]; infer_instance
  have hgi' : GeometricallyIntegral (O.ι ≫ p') := by
    have : MorphismProperty.RespectsIso @GeometricallyIntegral :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    rw [hOp]; exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral φ.inv _).mpr hgi
  have he' : (e ≫ φ.hom) ≫ O.ι ≫ p' = 𝟙 _ := by
    simp only [p', Category.assoc]; rw [reassoc_of% hφ]; exact he
  have hpY : p' ≫ V.ι ≫ A.hom = i0 ≫ Y.hom := by
    simp only [p', Category.assoc]; rw [reassoc_of% hpv, Over.w v]
  have hcover : O ⊔ p' ⁻¹ᵁ UT = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have hz : x.left (i0 z) ∈ W := z.2
    have h' : x.left (i0 z) ∈ ((A.hom ⁻¹ᵁ U ⊔ V : A.left.Opens) : Set A.left) := hWUV hz
    rw [TopologicalSpace.Opens.coe_sup] at h'
    rcases h' with h | h
    · right
      show (V.ι ≫ A.hom) (p' z) ∈ U
      rw [← Scheme.Hom.comp_apply, hpY, ← Over.w x, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact h
    · left
      exact h
  have key : ∀ c' : Pic (x.left ⁻¹ᵁ W).toScheme, pull O.ι c' = 0 → pull (p' ⁻¹ᵁ UT).ι c' = 0 →
      c' = 0 := fun c' h1 h2 =>
    GlobalTheory.T.picardClass_eq_zero_of_zero_dense_open_and_section_open V.toScheme (x.left ⁻¹ᵁ W).toScheme ((GlobalTheory.isNormalScheme_iff _).mp hVn) UT hUT p'
      O (e ≫ φ.hom) hsm' hgi' he' hcover c' h1 h2
  apply key
  · rw [← pull_comp]
    have hfac : O.ι ≫ (x.left ∣_ W) = φ.inv ≫ (x.left ∣_ V) ≫ A.left.homOfLE hV := by
      rw [← cancel_mono W.ι]
      simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
      rw [← reassoc_of% hφ]
      simp [i0]
    rw [hfac, pull_comp, pull_comp, map_nsmul, hc, smul_zero, map_zero, map_zero]
  · rw [← pull_comp]
    let j := (p' ⁻¹ᵁ UT).ι
    let Y' : Over S := Over.mk (j ≫ i0 ≫ Y.hom)
    let q : Y' ⟶ Y := Over.homMk (j ≫ i0) (by simp [Y'])
    refine GlobalTheory.T.twice_picardClass_eq_zero_of_translates_mem_open S A hA U V W hV hUW c hc Y' (q ≫ x) (q ≫ a) (q ≫ v) ?_ ?_ ?_
      (j ≫ (x.left ∣_ W)) ?_
    · intro y
      show (j ≫ i0 ≫ Y.hom) y ∈ U
      rw [← hpY]
      exact y.2
    · intro y
      have : (q ≫ v).left = (j ≫ i0 ≫ p) ≫ V.ι := by simp [q, hpv]
      rw [this, Scheme.Hom.comp_apply]
      exact ((j ≫ i0 ≫ p) y).2
    · intro y
      simp only [← GrpObj.comp_inv, ← MonObj.comp_mul, Over.comp_left, Scheme.Hom.comp_apply]
      exact hmem _
    · simp [q, j, i0, morphismRestrict_ι]

end GlobalTheory
