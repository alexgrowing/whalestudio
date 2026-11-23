import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTwoOpenCoverUnitsSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAboveDenseOpenEqGlobalMulPullbackStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem bijective_appLE_ι {Z : Scheme.{0}} (O W : Z.Opens) (hW : W ≤ O) (W' : O.toScheme.Opens)
    (h : W' = O.ι ⁻¹ᵁ W) : Function.Bijective (O.ι.appLE W W' h.le) := by
  subst h
  have : IsIso (O.ι.app W) := Scheme.Hom.isIso_app _ _ (by simpa using hW)
  rw [← Scheme.Hom.app_eq_appLE]
  exact ConcreteCategory.bijective_of_isIso _

theorem eq_zero_of_pull_eq_zero : ∀ (T Z : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → ∀ (U : T.Opens), (U : Set T).Nonempty → ∀ (p : Z ⟶ T) (O : Z.Opens) (e : T ⟶ O.toScheme), Smooth (O.ι ≫ p) → GeometricallyIntegral (O.ι ≫ p) → e ≫ O.ι ≫ p = 𝟙 _ → O ⊔ p ⁻¹ᵁ U = ⊤ → ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull (p ⁻¹ᵁ U).ι c = 0 → c = 0 := by
  intro T Z _ _ hT U hU p O e hs hg he hcov
  refine GlobalTheory.T.cechPicard_eq_zero_of_twoOpen_cover_units_split Z O (p ⁻¹ᵁ U) hcov fun F => ?_
  have h1 : (O.ι ≫ p) ⁻¹ᵁ U = O.ι ⁻¹ᵁ (O ⊓ p ⁻¹ᵁ U) := by
    rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq, Scheme.Hom.comp_preimage]
  have h2 : (⊤ : O.toScheme.Opens) = O.ι ⁻¹ᵁ O := by simp
  have b1 := bijective_appLE_ι O (O ⊓ p ⁻¹ᵁ U) inf_le_left _ h1
  have b2 := bijective_appLE_ι O O le_rfl _ h2
  obtain ⟨G, w, hGw⟩ := GlobalTheory.T.unit_above_dense_open_eq_global_mul_pullback T O hT U hU (O.ι ≫ p) e hs hg he
    (Units.map (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom.toMonoidHom F)
  let ε := RingEquiv.ofBijective (O.ι.appLE O ⊤ h2.le).hom b2
  refine ⟨Units.map ε.symm.toMonoidHom G, pullU p U w, ?_⟩
  apply Units.ext
  apply b1.1
  have hv := congrArg Units.val hGw
  have hG : (O.ι.appLE O ⊤ h2.le).hom (ε.symm G) = G := ε.apply_symm_apply _
  change (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom F =
    O.toScheme.presheaf.map (homOfLE le_top).op (G : Γ(O, ⊤)) * (O.ι ≫ p).app U (w : Γ(T, U)) at hv
  change (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom F = (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom
    (Z.presheaf.map (homOfLE inf_le_left).op (ε.symm G) *
      Z.presheaf.map (homOfLE inf_le_right).op (p.app U (w : Γ(T, U))))
  rw [hv, map_mul, ← hG]
  congr 1
  · rw [hG]
    conv_lhs => rw [← hG]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE]

end GlobalTheory.PicGlue
