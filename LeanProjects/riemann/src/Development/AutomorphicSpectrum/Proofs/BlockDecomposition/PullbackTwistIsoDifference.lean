import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLineBundleOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem lbIso_pull_quot_of_consecutive_pw : ∀ {X Y : Scheme.{0}} (b : Y ⟶ X) (A C : LB X) (N : LB Y) (n : ℤ), A.IsLB → C.IsLB → N.IsLB → LBIso (A.pull b) (pw N n) → LBIso (C.pull b) (pw N (n + 1)) → LBIso N ((tw C A (-1)).pull b) := by
  intro X Y b A C N n hA hC hN h1 h2
  have hAb := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hA b
  have hCb := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hC b
  have hT := GlobalTheory.AbLaw.isLB_tw hC hA (-1)
  have hTb := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hT b
  rw [← GlobalTheory.CechPic.cls_eq_iff hN hTb, GlobalTheory.CechPic.cls_pull hT b hTb]
  have e1 := (GlobalTheory.CechPic.cls_eq_iff hAb (GlobalTheory.AbLaw.isLB_pw hN n)).2 h1
  have e2 := (GlobalTheory.CechPic.cls_eq_iff hCb (GlobalTheory.AbLaw.isLB_pw hN (n + 1))).2 h2
  rw [GlobalTheory.CechPic.cls_pull hA b hAb, GlobalTheory.EffBound.cls_pw hN n] at e1
  rw [GlobalTheory.CechPic.cls_pull hC b hCb, GlobalTheory.EffBound.cls_pw hN (n + 1)] at e2
  have hT' : GlobalTheory.CechPic.cls (GlobalTheory.AbLaw.tw C A (-1)) hT
      = GlobalTheory.CechPic.cls C hC - GlobalTheory.CechPic.cls A hA := by
    show GlobalTheory.CechPic.cls (C.div (GlobalTheory.AbLaw.pw A (-(-1)))) hT = _
    rw [GlobalTheory.CechPic.cls_div hC (GlobalTheory.AbLaw.isLB_pw hA _) hT, GlobalTheory.EffBound.cls_pw hA]
    simp
  rw [hT', map_sub, e1, e2, add_smul, one_smul, add_sub_cancel_left]

end GlobalTheory.CompanionTheory.FormalAlg
