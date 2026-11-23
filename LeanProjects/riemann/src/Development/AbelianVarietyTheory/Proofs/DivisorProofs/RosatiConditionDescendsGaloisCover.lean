import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigidifiedFaithfullyFlatDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.RosatiDescent

open GlobalTheory.CechPic

theorem lift_left_fst {S : Scheme.{0}} {A T : Over S} (f g : T ⟶ A) :
    (lift f g).left ≫ (fst A A).left = f.left :=
  congrArg (fun q => q.left) (lift_fst f g)

theorem lift_left_snd {S : Scheme.{0}} {A T : Over S} (f g : T ⟶ A) :
    (lift f g).left ≫ (snd A A).left = g.left :=
  congrArg (fun q => q.left) (lift_snd f g)

theorem eSec_comp_of_isMonHom {S : Scheme.{0}} {A : Over S} [GrpObj A] (u : A ⟶ A) [IsMonHom u] :
    eSec A ≫ u.left = eSec A := by
  show (η[A] ≫ u).left = η[A].left
  rw [IsMonHom.one_hom]

theorem lbIso_act_descent : ∀ (O : Type) [Ring O] (star : O → O) (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (act : OActN O A) (act₀ : OActN O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ c, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ act.act (star c))).left)) → ∀ c, LBIso (P₀.pull (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left) (P₀.pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left) := by
  intro O _ star X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ act act₀ hG hA hA₀ gp hsq hP hP₀ iP _ hact hros c
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have hB : IsAbelianScheme (G2 A₀) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA₀ hA₀
  have h₁ := pull_isLB hP₀ (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left
  have h₂ := pull_isLB hP₀ (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left
  have hN := LB.isLB_div h₂ h₁
  have cN := cls_div h₂ h₁ hN
  rw [cls_pull hP₀, cls_pull hP₀] at cN
  have m₀ := act₀.hom c
  have m₀' := act₀.hom (star c)
  have c₁ : φ₂ ≫ (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left =
      (lift (fst A A ≫ act.act c) (snd A A)).left ≫ φ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = (_ ≫ _) ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst, Category.assoc, hsq.1, ← Category.assoc, lift_left_fst]
      show φ₂ ≫ (fst A₀ A₀).left ≫ (act₀.act c).left = (fst A A).left ≫ (act.act c).left ≫ φ
      rw [reassoc_of% hsq.1, hact]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = (_ ≫ _) ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd, Category.assoc, hsq.2, ← Category.assoc, lift_left_snd]
  have c₂ : φ₂ ≫ (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left =
      (lift (fst A A) (snd A A ≫ act.act (star c))).left ≫ φ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = (_ ≫ _) ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst, Category.assoc, hsq.1, ← Category.assoc, lift_left_fst]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = (_ ≫ _) ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd, Category.assoc, hsq.2, ← Category.assoc, lift_left_snd]
      show φ₂ ≫ (snd A₀ A₀).left ≫ (act₀.act (star c)).left = (snd A A).left ≫ (act.act (star c)).left ≫ φ
      rw [reassoc_of% hsq.2, hact]
  have e₁ : eSec (G2 A₀) ≫ (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left = eSec (G2 A₀) := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = _ ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst, GlobalTheory.SquareDescent.eSec_fst]
      show eSec (G2 A₀) ≫ (fst A₀ A₀).left ≫ (act₀.act c).left = _
      rw [reassoc_of% GlobalTheory.SquareDescent.eSec_fst, eSec_comp_of_isMonHom]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = _ ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd]
  have e₂ : eSec (G2 A₀) ≫ (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left = eSec (G2 A₀) := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = _ ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = _ ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd, GlobalTheory.SquareDescent.eSec_snd]
      show eSec (G2 A₀) ≫ (snd A₀ A₀).left ≫ (act₀.act (star c)).left = _
      rw [reassoc_of% GlobalTheory.SquareDescent.eSec_snd, eSec_comp_of_isMonHom]
  have hPφ : pull φ₂ (cls _ hP₀) = cls _ hP := ((cls_eq_iff hP (pull_isLB hP₀ φ₂)).2 iP).symm
  have hR : pull (lift (fst A A ≫ act.act c) (snd A A)).left (cls _ hP) =
      pull (lift (fst A A) (snd A A ≫ act.act (star c))).left (cls _ hP) :=
    (cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 (hros c)
  have hpb := GlobalTheory.SiegelDescent.isPullback_square gp.1 φ₂ hsq
  have z₁ : pull (eSec (G2 A₀)) (cls _ hN) = 0 := by
    rw [cN, map_sub, ← pull_comp, ← pull_comp, e₁, e₂, sub_self]
  have z₂ : pull (pullback.fst (G2 A₀).hom π) (cls _ hN) = 0 := by
    rw [cN, ← hpb.isoPullback_inv_fst, pull_comp, map_sub, ← pull_comp φ₂, ← pull_comp φ₂, c₁, c₂,
      pull_comp, pull_comp, hPφ, hR, sub_self, map_zero]
  obtain ⟨t, ht⟩ := GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns Y X π (G2 A₀) _ hB hN
    inferInstance inferInstance inferInstance
    ((cls_eq_zero_iff (pull_isLB hN _)).1 ((cls_pull hN _ _).trans z₁))
    ((cls_eq_zero_iff (pull_isLB hN _)).1 ((cls_pull hN _ _).trans z₂))
  have h0 : cls _ hN = 0 := (cls_eq_zero_iff hN).2 ⟨t, ht⟩
  rw [cN, sub_eq_zero, ← cls_pull hP₀ _ h₁, ← cls_pull hP₀ _ h₂] at h0
  exact (cls_eq_iff h₁ h₂).1 h0.symm

end GlobalTheory.RosatiDescent
