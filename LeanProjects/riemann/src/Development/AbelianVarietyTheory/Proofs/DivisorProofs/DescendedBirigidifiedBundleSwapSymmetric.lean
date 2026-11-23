import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidLineBundleIsoDescentAlongGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigidifiedFaithfullyFlatDescent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.DescSymm

open GlobalTheory.CechPic

theorem eSec_swap {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    eSec (A ⊗ A) ≫ (lift (snd A A) (fst A A)).left = eSec (A ⊗ A) := by
  apply GlobalTheory.SquareDescent.square_hom_ext A
  · rw [Category.assoc, ← Over.comp_left, lift_fst, GlobalTheory.SquareDescent.eSec_snd, GlobalTheory.SquareDescent.eSec_fst]
  · rw [Category.assoc, ← Over.comp_left, lift_snd, GlobalTheory.SquareDescent.eSec_fst, GlobalTheory.SquareDescent.eSec_snd]

theorem lbIso_swap : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := by
  intro X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ hπ hA hA₀ gp hsq hP hP₀ iP ⟨r, hr⟩ iS
  have := hπ.fin
  have := hπ.etale
  have := hπ.onto
  have hA₂₀ : IsAbelianScheme (G2 A₀) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA₀ hA₀
  have hpb := GlobalTheory.SiegelDescent.isPullback_square gp.1 φ₂ hsq
  have hsw : (lift (snd A A) (fst A A)).left ≫ φ₂ = φ₂ ≫ (lift (snd A₀ A₀) (fst A₀ A₀)).left := by
    apply GlobalTheory.SquareDescent.square_hom_ext A₀
    · rw [Category.assoc, hsq.1, Category.assoc, ← Over.comp_left, lift_fst, ← Category.assoc, ← Over.comp_left,
        lift_fst, hsq.2]
    · rw [Category.assoc, hsq.2, Category.assoc, ← Over.comp_left, lift_snd, ← Category.assoc, ← Over.comp_left,
        lift_snd, hsq.1]
  have h₂ := pull_isLB hP₀ (lift (snd A₀ A₀) (fst A₀ A₀)).left
  have hN := LB.isLB_div h₂ hP₀
  have cN := (CechPic.cls_div h₂ hP₀ hN).trans (by rw [CechPic.cls_pull hP₀ _ h₂])
  have z₀ : CechPic.pull (eSec (G2 A₀)) (CechPic.cls _ hP₀) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB hP₀ _)).2 ⟨r, hr⟩
  have c₁ : CechPic.cls _ hP = CechPic.pull φ₂ (CechPic.cls _ hP₀) :=
    (CechPic.cls_eq_iff hP (pull_isLB hP₀ _)).2 iP
  have c₂ : CechPic.cls _ hP = CechPic.pull (lift (snd A A) (fst A A)).left (CechPic.cls _ hP) :=
    ((CechPic.cls_eq_iff hP (pull_isLB hP _)).2 iS).trans (CechPic.cls_pull hP _ _)
  refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns Y X π (G2 A₀) _ hA₂₀ hN
    inferInstance inferInstance inferInstance ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
  · rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, eSec_swap, z₀, sub_zero]
  · rw [CechPic.cls_pull hN, cN, ← hpb.isoPullback_inv_fst, CechPic.pull_comp, map_sub, ← CechPic.pull_comp φ₂,
      ← hsw, CechPic.pull_comp, ← c₁, ← c₂, sub_self, map_zero]

end GlobalTheory.DescSymm
