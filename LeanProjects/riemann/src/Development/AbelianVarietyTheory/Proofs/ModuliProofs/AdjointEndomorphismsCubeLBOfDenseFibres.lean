import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawReducedBaseAbelianSchemeOfDenseFibresStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open CechPic

theorem CechPic.lam_pull_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' T' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (c : Pic G.left) (x y : T' ⟶ G') :
    lam (pull φ c) x y = lam c (pushHom h T' x) (pushHom h T' y) := by
  rw [lam, lam, ← map_mul, ← map_one (pushHom h T')]
  simp only [← pull_comp]
  rfl

theorem adjoint_cubeLB_of_dense_fibres : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (u v : A ⟶ A), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → IsMonHom u → IsMonHom v → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (_ : IsCommMonObj G) (φ : G.left ⟶ A.left) (L' : LB G.left) (u' v' : G ⟶ G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ L'.IsLB ∧ LBIso L' (L.pull φ) ∧ u'.left ≫ φ = φ ≫ u.left ∧ v'.left ≫ φ = φ ≫ v.left ∧ LBIso (cubeLB G ![fst G G ≫ u', snd G G] L') (cubeLB G ![fst G G, snd G G ≫ v'] L')} → LBIso (cubeLB A ![fst A A ≫ u, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ v] L) := by
  intro hG S _ A _ _ L u v hA hL hamp hu hv hd
  have := hA.smooth
  have : IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  have hp : IsPullback (snd A A).left (fst A A).left A.hom A.hom :=
    (IsPullback.of_hasPullback A.hom A.hom).flip
  have h₁ : (cubeLB A ![fst A A ≫ u, snd A A] L).IsLB := LB.isLB_linComb hL _ _
  have h₂ : (cubeLB A ![fst A A, snd A A ≫ v] L).IsLB := LB.isLB_linComb hL _ _
  have hN := LB.isLB_div h₂ h₁
  refine GlobalTheory.T.seesaw_reduced_base_abelianScheme_of_dense_fibres hG S A L hA hL hamp A.left (A ⊗ A).left A.hom (snd A A).left (fst A A).left _ hp hN
    ((hd.preimage A.hom.isOpenMap).mono ?_) (lift (𝟙 A) (1 : A ⟶ A)).left ?_ ?_
  · rintro a ⟨K, _, x, G, _, _, φ, L', u', v', ⟨q, hq⟩, h, hL', hiso, hu', hv', H⟩
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback h.1 a q hq.symm
    let U : Over.mk ((G ⊗ G).hom ≫ x) ⟶ A ⊗ A := lift (pushHom h _ (fst G G)) (pushHom h _ (snd G G))
    have e₁ : U.left ≫ (fst A A).left = (fst G G).left ≫ φ :=
      congrArg (fun q => q.left) (lift_fst (pushHom h _ (fst G G)) (pushHom h _ (snd G G)))
    have e₂ : U.left ≫ (snd A A).left = (snd G G).left ≫ φ :=
      congrArg (fun q => q.left) (lift_snd (pushHom h _ (fst G G)) (pushHom h _ (snd G G)))
    have P : IsPullback U.left (fst G G).left (fst A A).left φ := by
      have B := (IsPullback.of_hasPullback G.hom G.hom).flip.paste_horiz h.1
      refine IsPullback.of_right ?_ e₁ hp
      rw [e₂, h.1.w]
      exact B
    have push : ∀ {w' : G ⟶ G} {w : A ⟶ A}, w'.left ≫ φ = φ ≫ w.left → ∀ y : G ⊗ G ⟶ G,
        pushHom h _ (y ≫ w') = pushHom h _ y ≫ w := fun hw y => Over.OverMorphism.ext (by
      show (y.left ≫ _) ≫ _ = (y.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
    refine ⟨G.left.residueField z, inferInstance, G.left.fromSpecResidueField z ≫ φ,
      pullback (fst G G).left (G.left.fromSpecResidueField z), pullback.fst _ _ ≫ U.left,
      pullback.snd _ _, ⟨IsLocalRing.closedPoint (G.left.residueField z), ?_⟩,
      (IsPullback.of_hasPullback _ _).paste_horiz P, ?_⟩
    · rw [← hz]
      exact congrArg φ (Scheme.fromSpecResidueField_apply z _)
    · have h₁' : (cubeLB G ![fst G G ≫ u', snd G G] L').IsLB := LB.isLB_linComb hL' _ _
      have h₂' : (cubeLB G ![fst G G, snd G G ≫ v'] L').IsLB := LB.isLB_linComb hL' _ _
      have H' := (cls_eq_iff h₁' h₂').2 H
      rw [cls_cube_two hL', cls_cube_two hL', (cls_eq_iff hL' (pull_isLB hL φ)).2 hiso, cls_pull hL,
        lam_pull_of_isGrpPullback h, lam_pull_of_isGrpPullback h, push hu', push hv'] at H'
      have j : pull U.left (cls _ h₂ - cls _ h₁) = 0 := by
        rw [cls_cube_two hL, cls_cube_two hL, map_sub, pull_lam, pull_lam, lift_fst,
          lift_snd, lift_fst_assoc, lift_snd_assoc]
        exact sub_eq_zero.2 H'.symm
      refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
      rw [cls_pull hN, cls_div h₂ h₁]
      exact (pull_comp _ _ _).trans ((congrArg _ j).trans (map_zero _))
  · rw [← Over.comp_left, lift_fst, Over.id_left]
  · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
    rw [cls_pull hN, cls_div h₂ h₁, cls_cube_two hL, cls_cube_two hL, map_sub, pull_lam, pull_lam, lift_fst,
      lift_snd, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, lam_one_right, lam_one_right, sub_self]

end GlobalTheory
