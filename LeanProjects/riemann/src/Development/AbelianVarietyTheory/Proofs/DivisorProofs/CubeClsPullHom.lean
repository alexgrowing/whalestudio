import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProdUnif
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HypSEisensteinCurve
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProd.GAdjFst

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem psum_comp_hom {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f]
    {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    psum G x I ≫ f = psum H (fun i => x i ≫ f) I :=
  psum_hom (MonoidHom.mk' (fun z : T ⟶ G => z ≫ f) fun a b => MonObj.mul_comp a b f) x I

theorem cubeCls_pull_hom {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H)
    [IsMonHom f] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic H.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G x (pull f.left c) = GlobalTheory.ZH.EndoExtend.cubeCls H (fun i => x i ≫ f) c := by
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← pull_comp, ← Over.comp_left, psum_comp_hom]

theorem cubeCls_add {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G))
    (a b : Pic G.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G x (a + b) = GlobalTheory.ZH.EndoExtend.cubeCls G x a + GlobalTheory.ZH.EndoExtend.cubeCls G x b := by
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  simp only [map_add, smul_add, Finset.sum_add_distrib]

theorem cubeCls_one_left {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (y : T ⟶ G) (c : Pic G.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G ![1, y] c = 0 := by
  have h := GlobalTheory.ZH.CubeRootAut.cubeCls_pair (1 : T ⟶ G) y c
  have e : GlobalTheory.ZH.EndoExtend.cubeCls G ![1, y] c = GlobalTheory.TripleProd.cubeCls ![1, y] c := rfl
  rw [e, h, _root_.one_mul]
  abel

end GlobalTheory.MumProd.GAdjFst

theorem GlobalTheory.MumProd.gAdj_prod_fst : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hU
  obtain ⟨w, hw⟩ := hU.wL
  have hL := U.LG.isLB
  have hL₁ := U₁.LG.isLB
  have hL₂ := U₂.LG.isLB
  have hE : (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left).IsLB :=
    GlobalTheory.CechPic.isLB_tens (pull_isLB hL₁ _) (pull_isLB hL₂ _)
  have e0 : GlobalTheory.CechPic.cls _ hL = GlobalTheory.CechPic.pull (fst G₁ G₂).left (GlobalTheory.CechPic.cls _ hL₁) +
      GlobalTheory.CechPic.pull (snd G₁ G₂).left (GlobalTheory.CechPic.cls _ hL₂) :=
    (GlobalTheory.CechPic.cls_eq_iff hL hE).2 ⟨w, hw⟩
  unfold GAdj
  refine (GlobalTheory.CechPic.cls_eq_iff _ _).1 ((GlobalTheory.ZH.EndoExtend.cls_cubeLB (G₁ ⊗ G₂) _ hL).trans
    (Eq.trans ?_ (GlobalTheory.ZH.EndoExtend.cls_cubeLB G₁ _ hL₁).symm))
  rw [e0,
    GlobalTheory.MumProd.GAdjFst.cubeCls_add, GlobalTheory.MumProd.GAdjFst.cubeCls_pull_hom,
    GlobalTheory.MumProd.GAdjFst.cubeCls_pull_hom]
  have h₁ : (fun i => (![fst G₁ (G₁ ⊗ G₂) ≫ lift (𝟙 G₁) 1, snd G₁ (G₁ ⊗ G₂)] : Fin 2 → _) i ≫ fst G₁ G₂) =
      ![fst G₁ (G₁ ⊗ G₂), snd G₁ (G₁ ⊗ G₂) ≫ fst G₁ G₂] := by
    funext i; fin_cases i <;> simp
  have h₂ : (fun i => (![fst G₁ (G₁ ⊗ G₂) ≫ lift (𝟙 G₁) 1, snd G₁ (G₁ ⊗ G₂)] : Fin 2 → _) i ≫ snd G₁ G₂) =
      ![1, snd G₁ (G₁ ⊗ G₂) ≫ snd G₁ G₂] := by
    funext i; fin_cases i <;> simp
  rw [h₁, h₂, GlobalTheory.MumProd.GAdjFst.cubeCls_one_left, add_zero]
