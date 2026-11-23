import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.FormFinite

open GlobalTheory.CechPic GlobalTheory.AmpleStabFinite

theorem lam_inv_eq {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (m l : CechPic.Pic A.left) (s : A ⟶ A)
    [IsMonHom s] (h : ∀ u v : T ⟶ A, lam m u v = lam l u (v ≫ s)) {x y : T ⟶ A} (e : x ≫ s = y ≫ s) :
    lam m x⁻¹ x = lam m y y⁻¹ := by
  rw [h, e, ← h, lam_comm, h, GrpObj.inv_comp, e, ← GrpObj.inv_comp, ← h]

theorem isFinite_of_lam_eq {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] [IsProper A.hom]
    {M : LB A.left} (hM : IsAmpleLB M) (l : CechPic.Pic A.left) (s : A ⟶ A) [IsMonHom s]
    (h : ∀ (T : Over (Sp K)) (u v : T ⟶ A), lam (cls M hM.isLB) u v = lam l u (v ≫ s)) : IsFinite s.left := by
  obtain ⟨n, -, N, t, hc, ha⟩ := hM.exists_cover
  have : IsProper (s.left ≫ A.hom) := by rw [Over.w s]; infer_instance
  have : IsProper s.left := .of_comp _ A.hom
  suffices LocallyQuasiFinite s.left from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => ?_
  rcases Set.eq_empty_or_nonempty (s.left ⁻¹' {z}) with h0 | ⟨a, hz⟩
  · rw [h0]; exact Set.finite_empty
  let k : Type := A.left.residueField a
  let y₀ : Spec (CommRingCat.of k) ⟶ A.left := A.left.fromSpecResidueField a
  let P : Over (Sp K) := Over.mk (y₀ ≫ A.hom)
  let y : P ⟶ A := Over.homMk y₀ rfl
  let π : pullback s.left (y₀ ≫ s.left) ⟶ A.left := pullback.fst _ _
  let q : pullback s.left (y₀ ≫ s.left) ⟶ Spec (CommRingCat.of k) := pullback.snd _ _
  have w : π ≫ s.left = q ≫ y₀ ≫ s.left := pullback.condition
  let F : Over (Sp K) := Over.mk (π ≫ A.hom)
  let x : F ⟶ A := Over.homMk π rfl
  let r : F ⟶ P := Over.homMk q (by
    change q ≫ y₀ ≫ A.hom = π ≫ A.hom
    rw [← Over.w s, reassoc_of% w])
  have : IsAffineHom (y₀ ≫ s.left) := .of_comp _ A.hom
  have : IsAffineHom π := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
    (IsPullback.of_hasPullback s.left (y₀ ≫ s.left)).flip this
  have key := lam_inv_eq _ l s (h F) (x := x) (y := r ≫ y) (Over.OverMorphism.ext w)
  have triv : ∀ (b : P ⟶ A) (c : CechPic.Pic A.left), CechPic.pull (r ≫ b).left c = 0 := fun b c => by
    rw [Over.comp_left, pull_comp, pull_spec_local (K := k) b.left, map_zero]
  have one : ∀ c : CechPic.Pic A.left, CechPic.pull (1 : F ⟶ A).left c = 0 := fun c => by
    rw [← MonObj.comp_one r, triv]
  simp only [lam, inv_mul_cancel, ← GrpObj.comp_inv, ← MonObj.comp_mul, one, triv] at key
  have : CompactSpace ↥(pullback s.left (y₀ ≫ s.left)) := QuasiCompact.compactSpace_of_compactSpace q
  have : (pullback s.left (y₀ ≫ s.left)).IsQuasiAffine := quasiAffine_of_pull_add π (x⁻¹).left
    (isLB_lbPow hM.isLB n) t hc ha (by
      have e : CechPic.pull x.left (cls M hM.isLB) + CechPic.pull (x⁻¹).left (cls M hM.isLB) = 0 := by
        linear_combination (norm := abel) - key
      change CechPic.pull x.left _ + CechPic.pull (x⁻¹).left _ = 0
      rw [cls_lbPow hM.isLB, map_nsmul, map_nsmul, ← nsmul_add, e, nsmul_zero])
  have : IsAffine (pullback s.left (y₀ ≫ s.left)) := isAffine_of_quasiAffine q
  have : IsFinite q := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set ↥(pullback s.left (y₀ ≫ s.left))).Finite :=
    (q.finite_preimage_singleton (IsLocalRing.closedPoint k)).subset fun t _ => Subsingleton.elim _ _
  refine (hfin.image π).subset fun b hb => ?_
  have e : s.left b = (y₀ ≫ s.left) (IsLocalRing.closedPoint k) := by
    have e₀ : y₀ (IsLocalRing.closedPoint k) = a := Scheme.fromSpecResidueField_apply a _
    exact (show s.left b = z from hb).trans ((show s.left a = z from hz).symm.trans (congrArg s.left e₀).symm)
  obtain ⟨c, hc, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s.left) (g := y₀ ≫ s.left) b _ e
  exact ⟨c, trivial, hc⟩

theorem isFinite_and_surjective_of_formIs : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → Out.RelAmple P.A M → FormIs P M s → IsFinite s.left ∧ Surjective s.left := by
  intro _ _ K _ _ P M s hM hA ⟨hs, H⟩
  have := P.isAb.proper
  have := P.isAb.comm
  have e := (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb P.isLB _ _)).2 H
  have e' := (cls_cube_two hM _ _ _).symm.trans (e.trans (cls_cube_two P.isLB _ _ _))
  have hf : IsFinite s.left :=
    isFinite_of_lam_eq (isAmpleLB_of_relAmple_of_isAffine P.A hM hA) (cls P.L P.isLB) s fun T u v => by
      simpa only [pull_lam, lift_fst, lift_snd, lift_snd_assoc] using congrArg (CechPic.pull (lift u v).left) e'
  exact ⟨hf, (flat_and_surjective_of_isFinite_abelianEnd
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K P.A P.isAb s hs hf).2⟩

end GlobalTheory.FormFinite
