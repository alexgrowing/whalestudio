import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory

theorem cechPic_sp_field_eq_zero (K : Type) [Field K] (c : GlobalTheory.CechPic.Pic (Sp K)) : c = 0 := by
  obtain ⟨L, hL, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  exact (GlobalTheory.CechPic.cls_eq_zero_iff hL).2 (GlobalTheory.LB.exists_isGen_of_isLocalRing hL)

theorem pull_nsmul_cls_eq_zero_of_comap : ∀ {S S' X' : Scheme.{0}} (B : GlobalTheory.EffCartierData S') (n : ℕ) (h : S ⟶ S') (q : S ⟶ X')
    (I : X'.IdealSheafData), IsIso h → FinalTheorems.EffCartier I → I.comap q = (B.idealSheaf ^ n).comap h →
    ∀ (W : Scheme.{0}) (K : Type) [Field K] (g : W ⟶ S) (a : W ⟶ Sp K) (x0 : Sp K ⟶ X'), g ≫ q = a ≫ x0 →
    GlobalTheory.CechPic.pull (g ≫ h) (n • GlobalTheory.CechPic.cls B.lb B.isLB_lb) = 0 := by
  intro S S' X' B n h q I hh hI hc W K _ g a x0 hg
  obtain ⟨D, hD⟩ := GlobalTheory.EffCartierData.exists_idealSheaf_eq hI
  have kh : (B.nsmul n).KeepsRegular h := (B.nsmul n).keepsRegular_of_flat h
  have e1 : ((B.nsmul n).pull h kh).idealSheaf = D.idealSheaf.comap q := by
    rw [GlobalTheory.EffCartierData.idealSheaf_pull, GlobalTheory.EffCartierData.idealSheaf_nsmul, hD, hc]
  have kq : D.KeepsRegular q := (D.keepsRegular_iff_effCartier q).2
    (e1 ▸ ((B.nsmul n).pull h kh).effCartier_idealSheaf)
  have e2 : ((B.nsmul n).pull h kh).idealSheaf = (D.pull q kq).idealSheaf := by
    rw [e1, GlobalTheory.EffCartierData.idealSheaf_pull]
  have i1 := ((B.nsmul n).pull h kh).lbIso_of_idealSheaf_eq (D.pull q kq) e2
  have key : GlobalTheory.CechPic.pull h (n • GlobalTheory.CechPic.cls B.lb B.isLB_lb) =
      GlobalTheory.CechPic.pull q (GlobalTheory.CechPic.cls D.lb D.isLB_lb) := by
    rw [← GlobalTheory.CechPic.cls_lbPow B.isLB_lb n (B.isLB_lbPow n),
      ← (GlobalTheory.CechPic.cls_eq_iff (B.nsmul n).isLB_lb (B.isLB_lbPow n)).2 (B.lbIso_nsmul n),
      ← GlobalTheory.CechPic.cls_pull (B.nsmul n).isLB_lb h (pull_isLB (B.nsmul n).isLB_lb h),
      ← GlobalTheory.CechPic.cls_pull D.isLB_lb q (pull_isLB D.isLB_lb q),
      ← (GlobalTheory.CechPic.cls_eq_iff ((B.nsmul n).pull h kh).isLB_lb (pull_isLB (B.nsmul n).isLB_lb h)).2
        ((B.nsmul n).lbIso_pull h kh),
      ← (GlobalTheory.CechPic.cls_eq_iff (D.pull q kq).isLB_lb (pull_isLB D.isLB_lb q)).2 (D.lbIso_pull q kq)]
    exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 i1
  rw [GlobalTheory.CechPic.pull_comp, key, ← GlobalTheory.CechPic.pull_comp, hg, GlobalTheory.CechPic.pull_comp,
    cechPic_sp_field_eq_zero K (GlobalTheory.CechPic.pull x0 _), map_zero]

end GlobalTheory
