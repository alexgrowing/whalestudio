import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelActionIsPullbackProdMapTorsorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsCharacterUnitKernelActionStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAppTopEqOfEffectiveEpi
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFlat
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CharKer

theorem pmap_eq_whiskerRight {S : Scheme.{0}} {A A' : Over S} (q : A ⟶ A') (T : Over S) : pmap q T = q ▷ T := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [pmap]

theorem isPullback_over_left {S : Scheme.{0}} {P X Y Z : Over S} {f : P ⟶ X} {g : P ⟶ Y} {h : X ⟶ Z} {k : Y ⟶ Z}
    (H : IsPullback f g h k) : IsPullback f.left g.left h.left k.left :=
  H.map (Over.forget S)

theorem res_res_units {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  apply Units.ext
  change _ = (X.presheaf.map ((homOfLE h₁).op ≫ (homOfLE h₂).op)).hom x.val
  rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]; rfl

theorem res_pullU_units {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) :
    pullU f V (res h x) = res (f.preimage_mono h) (pullU f U x) := by
  apply Units.ext
  have := f.naturality (homOfLE h).op
  change (X.presheaf.map (homOfLE h).op ≫ f.app V).hom x.val = _
  rw [this]; rfl

theorem mul_mul_inv_mul_inv_cancel {G : Type*} [CommGroup G] (c x y : G) : (c * x) * (c * y)⁻¹ = x * y⁻¹ := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]

theorem exists_equivGen : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → ∃ (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), M.IsLB ∧ IsEquivGen i q χ M e := by
  intro S A A' N T _ _ _ i q χ hi hq hfin hflat hsurj hker hχ
  have hloc := GlobalTheory.T.exists_nhds_characterUnit_kernel_action S A A' N T i q χ hi hq hfin hflat hsurj hker hχ
  have : Flat (pmap q T).left := by rw [pmap_eq_whiskerRight]; infer_instance
  have : Surjective (pmap q T).left := by rw [pmap_eq_whiskerRight]; infer_instance
  have : QuasiCompact (pmap q T).left := by rw [pmap_eq_whiskerRight]; infer_instance
  have hpb : IsPullback (prMap A N T).left (actMap i T).left (pmap q T).left (pmap q T).left :=
    isPullback_over_left (GlobalTheory.T.kernelAction_isPullback_prodMap_torsor S A A' N T i q hi hq hker)
  have hw : ∀ z, (pmap q T).left ((actMap i T).left z) = (pmap q T).left ((prMap A N T).left z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hpb.w]
  have inj : ∀ U : (A' ⊗ T).left.Opens, Function.Injective (pullU (pmap q T).left U) := fun U x y hxy =>
    Units.ext (ReciprocityTheory.ChartRestriction.G.DVR.TG.app_injective_of_flat_surj (pmap q T).left U (congrArg Units.val hxy))
  have desc : ∀ (U : (A' ⊗ T).left.Opens) (u : Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ U)ˣ),
      (∀ (W : (A ⊗ (N ⊗ T)).left.Opens) (h₁ : W ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U))
        (h₂ : W ≤ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U)),
        res h₁ (pullU (actMap i T).left _ u) = res h₂ (pullU (prMap A N T).left _ u)) →
      ∃ g : Γ((A' ⊗ T).left, U)ˣ, pullU (pmap q T).left U g = u := by
    intro U u hu
    have hg : (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U) ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U) :=
      fun z hz => show (pmap q T).left ((actMap i T).left z) ∈ U from (hw z) ▸ hz
    have key := GlobalTheory.FlatDescent.existsUnique_app_eq_iff (pmap q T).left hpb U _ rfl le_rfl hg u.val
    obtain ⟨a, ha, -⟩ := key.2 (congrArg Units.val (hu _ hg le_rfl)).symm
    obtain ⟨a, rfl⟩ := (GlobalTheory.FlatDescent.isUnit_app_iff (pmap q T).left U a).1 (ha ▸ u.isUnit)
    exact ⟨a, Units.ext ha⟩
  choose V hyV e he using hloc
  have hu : ∀ k l, ∃ g : Γ((A' ⊗ T).left, V k ⊓ V l)ˣ, pullU (pmap q T).left _ g =
      res ((pmap q T).left.preimage_mono inf_le_left) (e k) *
        (res ((pmap q T).left.preimage_mono inf_le_right) (e l))⁻¹ := fun k l => desc _ _ (by
    intro W h₁ h₂
    simp only [map_mul, map_inv, res_pullU_units, res_res_units]
    rw [he k W _ (h₂.trans ((prMap A N T).left.preimage_mono ((pmap q T).left.preimage_mono inf_le_left))),
      he l W _ (h₂.trans ((prMap A N T).left.preimage_mono ((pmap q T).left.preimage_mono inf_le_right))),
      mul_mul_inv_mul_inv_cancel])
  choose g hg using hu
  refine ⟨⟨(A' ⊗ T).left, V, g⟩, e, ⟨?_, ?_, ?_⟩, ?_, fun k W h₁ h₂ => he k W h₁ h₂⟩
  · exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyV y⟩
  · intro k
    apply inj
    simp only [res_pullU_units, hg, map_mul, map_inv, res_res_units, map_one, mul_inv_cancel]
  · intro a b c
    apply inj
    simp only [res_pullU_units, hg, map_mul, map_inv, res_res_units, _root_.mul_assoc, inv_mul_cancel_left]
  · intro k l W h₁ h₂ h₃
    simp only [res_pullU_units, hg, map_mul, map_inv, res_res_units, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]

end GlobalTheory.CharKer
