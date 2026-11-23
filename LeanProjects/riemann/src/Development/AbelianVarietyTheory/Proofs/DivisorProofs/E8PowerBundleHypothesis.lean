import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerLiftCompProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataMatrixActionRingHomProperties
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

open GlobalTheory.Mum.Pow8

section Pairing

theorem comp_matAct_pr {S : Scheme.{0}} {G₀ : Over S} [GrpObj G₀] [IsCommMonObj G₀] {X : Over S}
    (x : X ⟶ powObj G₀ 8) (a : Matrix (Fin 8) (Fin 8) ℤ) (i : Fin 8) :
    (x ≫ matAct G₀ a) ≫ powPr G₀ i = ∏ j, (x ≫ powPr G₀ j) ^ a i j := by
  rw [Category.assoc, matAct_pr]
  exact GlobalTheory.Mum.TensAct.comp_prod_zpow x _ _

variable {S : Scheme.{0}} {G₀ : Over S} [GrpObj G₀] [IsCommMonObj G₀] {L : LB G₀.left} (hL : L.IsLB)

def formPair (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (x y : X ⟶ powObj G₀ 8) : GlobalTheory.CechPic.Pic X.left :=
  ∑ i, ∑ j, M i j • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ≫ powPr G₀ i) (y ≫ powPr G₀ j)

theorem cls_e8LB (W : Matrix (Fin 8) (Fin 8) ℤ) (h : (e8LB G₀ L W).IsLB) :
    GlobalTheory.CechPic.cls _ h = formPair hL W (𝟙 _) (𝟙 _) := by
  refine (GlobalTheory.CechPic.cls_linComb hL _ _ h).trans ?_
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  unfold formPair
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_four, lamPts, negε, GlobalTheory.CechPic.lam, Category.id_comp]
  simp [smul_add, sub_eq_add_neg]

theorem pull_cls_e8LB (W : Matrix (Fin 8) (Fin 8) ℤ) (h : (e8LB G₀ L W).IsLB) {X : Over S} (u : X ⟶ powObj G₀ 8) :
    GlobalTheory.CechPic.pull u.left (GlobalTheory.CechPic.cls _ h) = formPair hL W u u := by
  rw [cls_e8LB hL W h]
  unfold formPair
  simp only [map_sum, map_zsmul, GlobalTheory.CechPic.pull_lam, Category.id_comp]

variable (hΘ : ∃ t : LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.Theta G₀ L), t.IsGen)
include hΘ

theorem formPair_mul (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (u v : X ⟶ powObj G₀ 8) :
    formPair hL M (u * v) (u * v) = formPair hL M u u + formPair hL M v v + formPair hL (M + M.transpose) u v := by
  have hm : ∀ i, (u * v) ≫ powPr G₀ i = (u ≫ powPr G₀ i) * (v ≫ powPr G₀ i) := fun i => MonObj.mul_comp _ _ _
  have e1 : ∀ i j, GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) ((u * v) ≫ powPr G₀ i) ((u * v) ≫ powPr G₀ j) =
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (u ≫ powPr G₀ i) (u ≫ powPr G₀ j) +
        GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (v ≫ powPr G₀ i) (v ≫ powPr G₀ j) +
        (GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (u ≫ powPr G₀ i) (v ≫ powPr G₀ j) +
          GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (u ≫ powPr G₀ j) (v ≫ powPr G₀ i)) := by
    intro i j
    rw [hm, hm, GlobalTheory.CechPic.lam_mul_left hL hΘ, GlobalTheory.Mum.RosatiTens.lam_mul_right hL hΘ,
      GlobalTheory.Mum.RosatiTens.lam_mul_right hL hΘ, GlobalTheory.CechPic.lam_comm _ (v ≫ powPr G₀ i) (u ≫ powPr G₀ j)]
    abel
  unfold formPair
  simp only [e1, smul_add, Finset.sum_add_distrib, Matrix.add_apply, add_smul, Matrix.transpose_apply]
  congr 2
  exact Finset.sum_comm

theorem formPair_one (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} :
    formPair hL M (1 : X ⟶ powObj G₀ 8) 1 = 0 := by
  unfold formPair
  simp [MonObj.one_comp, GlobalTheory.CechPic.lam_one_left]

theorem lam_cls_e8LB (W : Matrix (Fin 8) (Fin 8) ℤ) (h : (e8LB G₀ L W).IsLB) {X : Over S}
    (x y : X ⟶ powObj G₀ 8) :
    GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls _ h) x y = formPair hL (W + W.transpose) x y := by
  unfold GlobalTheory.CechPic.lam
  simp only [pull_cls_e8LB hL W h]
  rw [formPair_mul hL hΘ, formPair_one hL hΘ]
  abel

theorem formPair_act_left (M a : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (x y : X ⟶ powObj G₀ 8) :
    formPair hL M (x ≫ matAct G₀ a) y = formPair hL (a.transpose * M) x y := by
  have s3 : ∀ F : Fin 8 → Fin 8 → Fin 8 → GlobalTheory.CechPic.Pic X.left,
      ∑ i, ∑ j, ∑ k, F i j k = ∑ k, ∑ j, ∑ i, F i j k := fun F =>
    calc ∑ i, ∑ j, ∑ k, F i j k = ∑ i, ∑ k, ∑ j, F i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, F i j k := Finset.sum_comm
      _ = ∑ k, ∑ j, ∑ i, F i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  unfold formPair
  simp only [comp_matAct_pr, GlobalTheory.Mum.RosatiTens.lam_prod_left hL hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  refine (s3 (fun i j k => (M i j * a i k) •
    GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ≫ powPr G₀ k) (y ≫ powPr G₀ j))).trans ?_
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
    rw [mul_comm]

theorem formPair_act_right (M a : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (x y : X ⟶ powObj G₀ 8) :
    formPair hL M x (y ≫ matAct G₀ a) = formPair hL (M * a) x y := by
  unfold formPair
  simp only [comp_matAct_pr, GlobalTheory.Mum.RosatiTens.lam_prod_right hL hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

end Pairing

theorem unimodular_symmetrised_matrix_adjugate_identities {W : Matrix (Fin 8) (Fin 8) ℤ} (hB : (W + W.transpose).det = 1) :
    (W + W.transpose) * ((W + W.transpose).adjugate * W) = W ∧
      (W + W.transpose).adjugate * W + (W + W.transpose).adjugate * W.transpose = 1 ∧
      ((W + W.transpose).adjugate * W).transpose * (W + W.transpose) =
        (W + W.transpose) * ((W + W.transpose).adjugate * W.transpose) := by
  have hBt : (W + W.transpose).transpose = W + W.transpose := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have h1 : (W + W.transpose) * (W + W.transpose).adjugate = 1 := by
    rw [Matrix.mul_adjugate, hB, one_smul]
  have h2 : (W + W.transpose).adjugate * (W + W.transpose) = 1 := by
    rw [Matrix.adjugate_mul, hB, one_smul]
  have hAt : (W + W.transpose).adjugate.transpose = (W + W.transpose).adjugate := by
    rw [Matrix.adjugate_transpose, hBt]
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  · rw [← Matrix.mul_add, h2]
  · rw [Matrix.transpose_mul, hAt, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem hypW_e8LB : ∀ (S : Scheme.{0}) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (P : GlobalTheory.UU.CP G₀)
    (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → GlobalTheory.LN.HypW (powObj G₀ 8) (GlobalTheory.PowE8.e8LB G₀ P.L.L W) := by
  intro S G₀ _ _ P W hW
  have hL : P.L.L.IsLB := P.L.isLB
  have hΘ : ∃ t : LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.Theta G₀ P.L.L), t.IsGen := ⟨P.c.1, P.c.2⟩
  have hE : (e8LB G₀ P.L.L W).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨h1, h2, h3⟩ := unimodular_symmetrised_matrix_adjugate_identities hW.2
  refine ⟨matAct G₀ ((W + W.transpose).adjugate * W), matAct G₀ ((W + W.transpose).adjugate * W.transpose),
    matAct_hom G₀ _, matAct_hom G₀ _, ?_, ?_, ?_⟩
  · rw [← matAct_one G₀, ← h2]
    refine eighthPowerGroupObj_hom_ext G₀ fun i => ?_
    rw [MonObj.mul_comp, matAct_pr, matAct_pr, matAct_pr, ← Finset.prod_mul_distrib]
    simp only [Matrix.add_apply, zpow_add]
  · have hC : (cubeLB (powObj G₀ 8) ![𝟙 (powObj G₀ 8), matAct G₀ ((W + W.transpose).adjugate * W)]
        (e8LB G₀ P.L.L W)).IsLB := LB.isLB_linComb hE _ _
    refine (GlobalTheory.CechPic.cls_eq_iff hE hC).1 ?_
    rw [GlobalTheory.CechPic.cls_cube_two hE _ _ hC, lam_cls_e8LB hL hΘ W hE, cls_e8LB hL W hE]
    have e := formPair_act_right hL hΘ (W + W.transpose) ((W + W.transpose).adjugate * W)
      (𝟙 (powObj G₀ 8)) (𝟙 (powObj G₀ 8))
    rw [Category.id_comp, h1] at e
    exact e.symm
  · have hC1 : (cubeLB (powObj G₀ 8) ![fst (powObj G₀ 8) (powObj G₀ 8) ≫ matAct G₀ ((W + W.transpose).adjugate * W),
        snd (powObj G₀ 8) (powObj G₀ 8)] (e8LB G₀ P.L.L W)).IsLB := LB.isLB_linComb hE _ _
    have hC2 : (cubeLB (powObj G₀ 8) ![fst (powObj G₀ 8) (powObj G₀ 8),
        snd (powObj G₀ 8) (powObj G₀ 8) ≫ matAct G₀ ((W + W.transpose).adjugate * W.transpose)]
        (e8LB G₀ P.L.L W)).IsLB := LB.isLB_linComb hE _ _
    refine (GlobalTheory.CechPic.cls_eq_iff hC1 hC2).1 ?_
    rw [GlobalTheory.CechPic.cls_cube_two hE _ _ hC1, GlobalTheory.CechPic.cls_cube_two hE _ _ hC2, lam_cls_e8LB hL hΘ W hE,
      lam_cls_e8LB hL hΘ W hE, formPair_act_left hL hΘ, formPair_act_right hL hΘ, h3]

end GlobalTheory.PowE8
end
