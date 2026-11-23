import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.PolClass

open GlobalTheory.CechPic

theorem lbIso_blowPol {X Z : Scheme.{0}} (π : Z ⟶ X) (ΩX : LB X) (ΩZ : LB Z) (DX : GlobalTheory.EffCartierData X)
    (EX : GlobalTheory.EffCartierData Z) (h : DX.KeepsRegular π) (k T : ℕ) (hΩX : ΩX.IsLB) (hΩZ : ΩZ.IsLB)
    (hΩ : LBIso ΩZ (ΩX.pull π)) :
    (GlobalTheory.CechPic.tens (lbPow ΩZ (T * k)) (GlobalTheory.CechPic.dual (((DX.pull π h).nsmul T).add EX).lb)).IsLB ∧
    LBIso (GlobalTheory.CechPic.tens (lbPow ΩZ (T * k)) (GlobalTheory.CechPic.dual (((DX.pull π h).nsmul T).add EX).lb))
      (GlobalTheory.CechPic.tens (lbPow ((GlobalTheory.CechPic.tens (lbPow ΩX k) (GlobalTheory.CechPic.dual DX.lb)).pull π) T)
        (GlobalTheory.CechPic.dual EX.lb)) := by
  set Dn := (DX.pull π h).nsmul T
  set E' := Dn.add EX
  have hZ : (lbPow ΩZ (T * k)).IsLB := LB.isLB_linComb hΩZ _ _
  have hL := isLB_tens hZ (isLB_dual E'.isLB_lb)
  have hXk : (lbPow ΩX k).IsLB := LB.isLB_linComb hΩX _ _
  have hM : (GlobalTheory.CechPic.tens (lbPow ΩX k) (GlobalTheory.CechPic.dual DX.lb)).IsLB := isLB_tens hXk (isLB_dual DX.isLB_lb)
  have hMp := pull_isLB hM π
  have hMpT : (lbPow ((GlobalTheory.CechPic.tens (lbPow ΩX k) (GlobalTheory.CechPic.dual DX.lb)).pull π) T).IsLB :=
    LB.isLB_linComb hMp _ _
  have hR := isLB_tens hMpT (isLB_dual EX.isLB_lb)
  refine ⟨hL, (cls_eq_iff hL hR).1 ?_⟩

  have eΩ : cls ΩZ hΩZ = pull π (cls ΩX hΩX) := (cls_eq_iff hΩZ (pull_isLB hΩX π)).2 hΩ
  have hDp := (DX.pull π h).isLB_lb
  have eDp : cls _ hDp = pull π (cls _ DX.isLB_lb) :=
    (cls_eq_iff hDp (pull_isLB DX.isLB_lb π)).2 (DX.lbIso_pull π h)
  have eDn : cls _ Dn.isLB_lb = T • cls _ hDp :=
    ((cls_eq_iff Dn.isLB_lb (LB.isLB_linComb hDp _ _)).2 ((DX.pull π h).lbIso_nsmul T)).trans
      (cls_lbPow hDp T _)
  have eE : cls _ EX.isLB_lb = cls _ E'.isLB_lb - cls _ Dn.isLB_lb :=
    ((cls_eq_iff EX.isLB_lb (LB.isLB_div E'.isLB_lb Dn.isLB_lb)).2 (Dn.lbIso_add EX)).trans
      (cls_div E'.isLB_lb Dn.isLB_lb _)
  rw [cls_tens hZ (isLB_dual E'.isLB_lb), cls_tens hMpT (isLB_dual EX.isLB_lb),
    cls_dual E'.isLB_lb, cls_dual EX.isLB_lb, cls_lbPow hΩZ, cls_lbPow hMp, cls_pull hM,
    cls_tens hXk (isLB_dual DX.isLB_lb), cls_dual DX.isLB_lb, cls_lbPow hΩX, eΩ, eE, eDn, eDp]
  simp only [map_add, map_neg, map_nsmul, smul_add, smul_neg, mul_smul]
  abel

end GlobalTheory.PolClass
