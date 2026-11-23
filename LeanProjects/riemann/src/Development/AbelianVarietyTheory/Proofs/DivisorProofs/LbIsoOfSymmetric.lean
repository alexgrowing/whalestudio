import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAbelianSchemeConstOverDualNumbers
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulEqZeroOfAppEqZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassEqZeroOfSquareZeroRetractionStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymFirstOrder
open GlobalTheory.CechPic

theorem lbIso_of_symmetric : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A']
    (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left),
    IsAbelianScheme A →
    IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i →
    IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → i ≫ q = 𝟙 _ →
    ∀ (L M : LB A'.left), L.IsLB → M.IsLB →
      LBIso (L.pull (GrpObj.inv : A' ⟶ A').left) L → LBIso (M.pull (GrpObj.inv : A' ⟶ A').left) M →
      LBIso (L.pull i) (M.pull i) → LBIso L M := by
  intro K _ _ A _ A' _ i q hA hi hq e L M hL hM hLs hMs hLM
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hA hq
  set c := cls L hL - cls M hM with hc
  have h0 : pull i c = 0 := by
    rw [hc, map_sub, ← cls_pull hL i (pull_isLB hL i), ← cls_pull hM i (pull_isLB hM i),
      (cls_eq_iff (pull_isLB hL i) (pull_isLB hM i)).2 hLM, sub_self]
  have hinv : pull (GrpObj.inv : A' ⟶ A').left c = c := by
    rw [hc, map_sub, ← cls_pull hL _ (pull_isLB hL _), ← cls_pull hM _ (pull_isLB hM _),
      (cls_eq_iff _ hL).2 hLs, (cls_eq_iff _ hM).2 hMs]
  have hlam := ConstTheta.lam_eq_zero GlobalTheory.laws_without_cohomology.1 hA' hi.1 c h0 (𝟙 A') (𝟙 A')⁻¹
  have einv : (𝟙 A')⁻¹ = (GrpObj.inv : A' ⟶ A') := by simp [Hom.inv_def]
  have hone : pull (1 : A' ⟶ A').left c = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨Q, hQ, hQc⟩ := cls_surj (pull (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left c)
    rw [← hQc, (cls_eq_zero_iff hQ).2 (LB.exists_isGen_of_isLocalRing hQ), map_zero]
  have htwo : 2 • c = 0 := by
    unfold lam at hlam
    rw [mul_inv_cancel, einv, hinv, hone, Over.id_left, pull_id] at hlam
    rw [two_nsmul, ← neg_eq_zero, neg_add]
    simpa [sub_eq_add_neg, add_assoc] using hlam

  have hsurj : Surjective i := by
    have : Surjective (GlobalTheory.DeRham.epsRed K) := ⟨fun x => by
      haveI := ConstTheta.subsingleton_sp (K := K)
      obtain ⟨t⟩ : Nonempty (Sp K) := inferInstance
      exact ⟨t, Subsingleton.elim _ _⟩⟩
    exact MorphismProperty.of_isPullback (P := @Surjective) hi.1.flip this
  have hiq : ∀ x, i (q x) = x := fun x => by
    obtain ⟨y, rfl⟩ := hsurj.surj x
    rw [← Scheme.Hom.comp_apply i q, e]; rfl
  have h2 : IsUnit (2 : Γ(A'.left, ⊤)) := by
    have u : IsUnit (2 : DualNumber K) := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [show TrivSqZeroExt.fst (2 : DualNumber K) = 2 from rfl]; exact isUnit_iff_ne_zero.2 two_ne_zero)
    have u' := (u.map (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom).map A'.hom.appTop.hom
    rwa [map_ofNat, map_ofNat] at u'
  have hsq : ∀ (W : A'.left.Opens) (f g : Γ(A'.left, W)), (i.app W).hom f = 0 → (i.app W).hom g = 0 → f * g = 0 := by
    refine SquareZero.mul_eq_zero_of_app_eq_zero (DualNumber K) K (TrivSqZeroExt.fstHom K K K).toRingHom
      TrivSqZeroExt.fst_surjective ?_ A'.left A.left A'.hom A.hom i hi.1
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro r hr s hs
    have hr' : r.fst = 0 := hr
    have hs' : s.fst = 0 := hs
    rw [Ideal.mem_bot]
    ext <;> simp [hr', hs']
  have hc0 := GlobalTheory.T.cechPicardClass_eq_zero_of_squareZero_retraction i q e hiq h2 hsq c h0 htwo
  exact (cls_eq_iff hL hM).1 (sub_eq_zero.1 hc0)

end GlobalTheory.SymFirstOrder
