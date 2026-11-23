import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfUnimodular
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.E8LatticePullbackGeneric

open GlobalTheory.CechPic

theorem sum_lamPts {S : Scheme.{0}} {G T : Over S} [GrpObj G] (x y : T ⟶ G) (c : Pic G.left) (w : ℤ) :
    ∑ k : Fin 4, (-(w * GlobalTheory.PolDeg.negε k)) • pull (GlobalTheory.PolDeg.lamPts x y k) c = w • lam c x y := by
  simp only [Fin.sum_univ_four, GlobalTheory.PolDeg.lamPts, GlobalTheory.PolDeg.negε, lam, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [smul_add, smul_sub, mul_neg, mul_one, neg_neg, neg_smul]
  first
  | (norm_num; done)
  | (norm_num; abel)
  | (push_cast; abel)
  | (rw [sub_eq_add_neg, sub_eq_add_neg]; congr 1 <;> [congr 1; skip] <;> norm_num)

theorem lam_pull_hom {S : Scheme.{0}} {G G' T : Over S} [GrpObj G] [GrpObj G'] (φ : G' ⟶ G) [IsMonHom φ]
    (c : Pic G.left) (x y : T ⟶ G') : lam (pull φ.left c) x y = lam c (x ≫ φ) (y ≫ φ) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, MonObj.mul_comp, MonObj.one_comp]

theorem pull_fst_lam {S S' : Scheme.{0}} (f : S' ⟶ S) {X G : Over S} [GrpObj G] (c : Pic G.left) (x x' : X ⟶ G) :
    GlobalTheory.CechPic.pull (pullback.fst X.hom f) (lam c x x') =
      lam (GlobalTheory.CechPic.pull (pullback.fst G.hom f) c) ((Over.pullback f).map x) ((Over.pullback f).map x') := by
  have hfst : ∀ z : X ⟶ G, pullback.fst X.hom f ≫ z.left = ((Over.pullback f).map z).left ≫ pullback.fst G.hom f :=
    fun z => by simp [pullback.lift_fst]
  simp only [lam, map_add, map_sub, ← pull_comp, hfst, Functor.map_mul, Functor.map_one]

open GlobalTheory.E8LatticePullbackGeneric GlobalTheory.CechPic in

theorem exists_polAV_gen : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ (A : PolAV (Sp (FractionRing V₁))) (gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  intro hL₁ _ _ V₁ _ _ _ _ D₀ G₀ _ _ A₀ U₀ _ W hW
  have := A₀.isAb.comm

  let c := GlobalTheory.EighthPowerFactor.siegOne hL₁.globalFns A₀.isAb A₀.isLB A₀.g
  have hc1 : RelAmple c.A c.diag := GlobalTheory.EighthPowerFactor.relAmple_diag_lam A₀.isAb A₀.isLB
    (GlobalTheory.Moduli.cube_of_isLB _ A₀ A₀.L A₀.isLB) A₀.ample
  have hb := GlobalTheory.EighthPower.isSymBilin hL₁.globalFns c hc1
  have hpw := GlobalTheory.PowGrp.powers _ _ _ 8 (powIsPowGrp A₀.A 8)
  have hu : ∀ (T : Over (Sp (FractionRing V₁))) (y : Fin 8 → (T ⟶ A₀.A)),
      ∃! x : T ⟶ powObj A₀.A 8, ∀ u, x ≫ powPr A₀.A u = y u := fun T y =>
    ⟨(powIsLimit A₀.A 8).lift (Fan.mk T y), fun u => (powIsLimit A₀.A 8).fac _ ⟨u⟩,
      fun x hx => (powIsLimit A₀.A 8).hom_ext fun ⟨u⟩ => by rw [(powIsLimit A₀.A 8).fac]; exact hx u⟩
  let Q : PolAV (Sp (FractionRing V₁)) :=
    { A := powObj A₀.A 8, isAb := hpw.2.2.2.1 A₀.isAb, g := 8 * A₀.g, smoothDim := hpw.2.2.1 _ A₀.smoothDim
      L := GlobalTheory.MatrixBundle.matLB c.P (powPr A₀.A) W, isLB := LB.isLB_linComb c.isLB _ _
      rigid := GlobalTheory.MatrixBundle.rigidified_matLB c.isLB hb (fun u => powPr.isMonHom A₀.A u)
      sym := GlobalTheory.MatrixBundle.sym_matLB c.isLB hb (fun u => powPr.isMonHom A₀.A u)
      ample := GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hL₁.globalFns _ _ 8 _ _ _ _ c _ (powPr A₀.A) W
        (fun u => powPr.isMonHom A₀.A u) hu hc1 hW.1
      ktriv := GlobalTheory.MatrixBundle.kTriv_matLB c.isLB hb (fun u => powPr.isMonHom A₀.A u) hu hW.2
        (fun T x hx => GlobalTheory.SiegelOfPolarised.eq_one_of_lam A₀.isLB A₀.ktriv x hx) }

  let F := Over.pullback (jK V₁)
  have hP : IsLimit (Fan.mk (F.obj (powObj G₀ 8)) fun u => F.map (powPr G₀ u)) :=
    isLimitFanMkObjOfIsLimit F _ _ (powIsLimit G₀ 8)
  let y : Fin 8 → (F.obj (powObj G₀ 8) ⟶ A₀.A) := fun u => F.map (powPr G₀ u) ≫ U₀.gen.hom
  let gen : F.obj (powObj G₀ 8) ≅ Q.A :=
    { hom := (powIsLimit A₀.A 8).lift (Fan.mk _ y)
      inv := hP.lift (Fan.mk Q.A fun u => powPr A₀.A u ≫ U₀.gen.inv)
      hom_inv_id := hP.hom_ext fun ⟨u⟩ => by
        simp only [Fan.mk_pt, Fan.mk_π_app, Category.assoc, Category.id_comp]
        erw [hP.fac (Fan.mk Q.A fun u => powPr A₀.A u ≫ U₀.gen.inv) ⟨u⟩]
        simp only [Fan.mk_π_app]
        erw [(powIsLimit A₀.A 8).fac_assoc (Fan.mk _ y) ⟨u⟩]
        simp [y]
      inv_hom_id := (powIsLimit A₀.A 8).hom_ext fun ⟨u⟩ => by
        simp only [Fan.mk_pt, Fan.mk_π_app, Category.assoc, Category.id_comp]
        erw [(powIsLimit A₀.A 8).fac (Fan.mk _ y) ⟨u⟩]
        simp only [Fan.mk_π_app, y]
        rw [← Category.assoc]
        erw [hP.fac (Fan.mk Q.A fun u => powPr A₀.A u ≫ U₀.gen.inv) ⟨u⟩]
        simp }
  have hgen : ∀ u, gen.hom ≫ powPr A₀.A u = y u := fun u => (powIsLimit A₀.A 8).fac _ ⟨u⟩
  have := U₀.gen_hom
  refine ⟨Q, gen, ?_, ?_⟩
  · refine GlobalTheory.EighthPowerFactor.isMonHom_of_coord (fun u => powPr.isMonHom A₀.A u) hu fun u => ?_
    rw [hgen u]
    infer_instance
  · have hA := A₀.isLB
    have hLG := U₀.LG.isLB
    have hQ : Q.L.IsLB := Q.isLB
    have hE : (GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).IsLB := LB.isLB_linComb hLG _ _
    have hext : pull (pullback.fst G₀.hom (jK V₁)) (cls _ hLG) = pull U₀.gen.hom.left (cls _ hA) := by
      obtain ⟨w, hw⟩ := U₀.ext
      have e := (cls_eq_iff (pull_isLB hA _) (pull_isLB hLG _)).2 ⟨w, hw⟩
      rw [cls_pull hA, cls_pull hLG] at e
      exact e.symm
    have key : ∀ x x' : powObj G₀ 8 ⟶ G₀, pull (pullback.fst (powObj G₀ 8).hom (jK V₁)) (lam (cls _ hLG) x x') =
        lam (cls _ hA) (F.map x ≫ U₀.gen.hom) (F.map x' ≫ U₀.gen.hom) := by
      intro x x'
      rw [pull_fst_lam, hext, lam_pull_hom]
    have hlam : cls c.P c.isLB = lam (cls _ hA) (fst A₀.A A₀.A) (snd A₀.A A₀.A) := cls_cube_two hA _ _ c.isLB
    have eL : pull gen.hom.left (cls Q.L hQ) =
        ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • lam (cls _ hA) (y uv.1) (y uv.2) := by
      rw [show cls Q.L hQ = _ from cls_linComb c.isLB
        (fun uv : Fin 8 × Fin 8 => (lift (powPr A₀.A uv.1) (powPr A₀.A uv.2)).left) (fun uv => W uv.1 uv.2) hQ, map_sum]
      refine Finset.sum_congr rfl fun uv _ => ?_
      rw [map_zsmul, hlam]
      erw [pull_lam, pull_lam]
      rw [lift_fst, lift_snd]
      erw [hgen, hgen]
    have eR : pull (pullback.fst (powObj G₀ 8).hom (jK V₁)) (cls _ hE) =
        ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • lam (cls _ hA) (y uv.1) (y uv.2) := by
      rw [show cls _ hE = _ from cls_linComb hLG (K := (Fin 8 × Fin 8) × Fin 4)
        (fun k => GlobalTheory.PolDeg.lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2)
        (fun k => -(W k.1.1 k.1.2 * GlobalTheory.PolDeg.negε k.2)) hE, Fintype.sum_prod_type]
      simp only [sum_lamPts, map_sum, map_zsmul, key, y]
    refine (cls_eq_iff (pull_isLB hQ _) (pull_isLB hE _)).1 ?_
    rw [cls_pull hQ, cls_pull hE, eL, eR]

end GlobalTheory.E8LatticePullbackGeneric

end
