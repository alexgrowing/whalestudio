import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isAffineOpen_inf_preimage_of_isPullback {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y}
    {iX : X ⟶ S} {iY : Y ⟶ S} (H : IsPullback p q iX iY) [IsAffine S] {U : X.Opens}
    {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) := by
  have : IsAffine _ := isAffineOpen_top S
  have : IsAffine _ := hU
  have : IsAffine _ := hV
  exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := V) (UX := U) le_top le_top
    rfl).isoPullback.hom

theorem appLE_appLE_of_comp {T X Y : Scheme.{0}} (f : T ⟶ X) (g : X ⟶ Y) (h : T ⟶ Y)
    (e : f ≫ g = h) {W : Y.Opens} {U : X.Opens} {N : T.Opens} (h1 : U ≤ g ⁻¹ᵁ W)
    (h2 : N ≤ f ⁻¹ᵁ U) (h3 : N ≤ h ⁻¹ᵁ W) (x : Γ(Y, W)) :
    (f.appLE U N h2).hom ((g.appLE W U h1).hom x) = (h.appLE W N h3).hom x := by
  subst e
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem functions_on_product_of_affine_opens : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (U : X.left.affineOpens) (V : Y.left.affineOpens), ∃ (W : (X ⊗ Y).left.affineOpens) (h₁ : W.1 ≤ (fst X Y).left ⁻¹ᵁ U.1) (h₂ : W.1 ≤ (snd X Y).left ⁻¹ᵁ V.1) (i₁ : Sec X.hom U.1 →ₐ[R] Sec (X ⊗ Y).hom W.1) (i₂ : Sec Y.hom V.1 →ₐ[R] Sec (X ⊗ Y).hom W.1), W.1 = (fst X Y).left ⁻¹ᵁ U.1 ⊓ (snd X Y).left ⁻¹ᵁ V.1 ∧ (∀ b, i₁ b = ((fst X Y).left.appLE U.1 W.1 h₁).hom b) ∧ (∀ b, i₂ b = ((snd X Y).left.appLE V.1 W.1 h₂).hom b) ∧ Function.Bijective (Algebra.TensorProduct.productMap i₁ i₂) := by
  intro R _ X Y U V
  have H : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom := .of_hasPullback _ _
  let W : (X ⊗ Y).left.affineOpens :=
    ⟨(fst X Y).left ⁻¹ᵁ U.1 ⊓ (snd X Y).left ⁻¹ᵁ V.1,
      isAffineOpen_inf_preimage_of_isPullback H U.2 V.2⟩
  have h₁ : W.1 ≤ (fst X Y).left ⁻¹ᵁ U.1 := inf_le_left
  have h₂ : W.1 ≤ (snd X Y).left ⁻¹ᵁ V.1 := inf_le_right
  let i₁ : Sec X.hom U.1 →ₐ[R] Sec (X ⊗ Y).hom W.1 :=
    { ((fst X Y).left.appLE U.1 W.1 h₁).hom with
      commutes' := fun r => by
        change ((fst X Y).left.appLE U.1 W.1 h₁).hom ((X.hom.appLE ⊤ U.1 le_top).hom _) =
          ((X ⊗ Y).hom.appLE ⊤ W.1 le_top).hom _
        exact appLE_appLE_of_comp _ _ _ (Over.w _) _ _ _ _ }
  let i₂ : Sec Y.hom V.1 →ₐ[R] Sec (X ⊗ Y).hom W.1 :=
    { ((snd X Y).left.appLE V.1 W.1 h₂).hom with
      commutes' := fun r => by
        change ((snd X Y).left.appLE V.1 W.1 h₂).hom ((Y.hom.appLE ⊤ V.1 le_top).hom _) =
          ((X ⊗ Y).hom.appLE ⊤ W.1 le_top).hom _
        exact appLE_appLE_of_comp _ _ _ (Over.w _) _ _ _ _ }
  refine ⟨W, h₁, h₂, i₁, i₂, rfl, fun b => rfl, fun b => rfl, ?_⟩
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := V.1) (UX := U.1) le_top le_top rfl).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) V.2 U.2)

  have po' : IsPushout (CommRingCat.ofHom (algebraMap R (Sec X.hom U.1)))
      (CommRingCat.ofHom (algebraMap R (Sec Y.hom V.1)))
      ((fst X Y).left.appLE U.1 W.1 h₁) ((snd X Y).left.appLE V.1 W.1 h₂) := by
    refine po.of_iso (Scheme.ΓSpecIso (CommRingCat.of R)) (Iso.refl (CommRingCat.of (Sec X.hom U.1)))
      (Iso.refl (CommRingCat.of (Sec Y.hom V.1)))
      (Iso.refl (CommRingCat.of (Sec (X ⊗ Y).hom W.1))) ?_ ?_ (by rfl) (by rfl)
    · ext r
      change (X.hom.appLE ⊤ U.1 le_top).hom r = (X.hom.appLE ⊤ U.1 le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))
      congr 1
      simp
    · ext r
      change (Y.hom.appLE ⊤ V.1 le_top).hom r = (Y.hom.appLE ⊤ V.1 le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))
      congr 1
      simp
  have h1 := CommRingCat.isPushout_tensorProduct R (Sec X.hom U.1) (Sec Y.hom V.1)
  let e := h1.isoIsPushout _ _ po'
  have he : e.hom = CommRingCat.ofHom (Algebra.TensorProduct.productMap i₁ i₂).toRingHom := by
    refine h1.hom_ext ?_ ?_
    · refine (h1.inl_isoIsPushout_hom _ _ po').trans ?_
      ext x
      exact (Algebra.TensorProduct.productMap_left_apply i₁ i₂ x).symm
    · refine (h1.inr_isoIsPushout_hom _ _ po').trans ?_
      ext x
      exact (Algebra.TensorProduct.productMap_right_apply i₁ i₂ x).symm
  have hb := ConcreteCategory.bijective_of_isIso e.hom
  rw [he] at hb
  exact hb

end GlobalTheory
