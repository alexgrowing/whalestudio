import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDeterminantIsoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagBoundaryIsoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorRelationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootDivisorSumTrivialStatement

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

theorem GlobalTheory.ShFam.lbIso_polPull : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp), LBIso ((Φ.C k).Y.lb ((∑ x : DV.Rt D.what₂.Tau N, (if (x.2 : ℕ) < j then 0 else 2 * s.T.m0 : ℕ) • divOf (Φ.C k) (rootExp S x)) - bdPull Φ k)) ((polLB s.T).pull ((Φ.C k).π ≫ genι s.T.Z)) := by
  intro D A N j S κ s Φ k
  have hO : (FlagMod.detOm s.T.Z).IsLB := (S.tor.isRec _ _ _).isLB_detOm
  have hB : s.T.BD.lb.IsLB := s.T.BD.isLB_lb
  have hP : (polLB s.T).IsLB := CechPic.isLB_tens (LB.isLB_linComb hO _ _) (CechPic.isLB_dual hB)
  rw [← CechPic.cls_eq_iff (isLB_toLB _) (pull_isLB hP _), ← toPic_apply, CechPic.cls_pull hP]
  have e1 : CechPic.cls (polLB s.T) hP = s.T.m0 • CechPic.cls _ hO - CechPic.cls _ hB := by
    have h := CechPic.cls_tens (A := lbPow (FlagMod.detOm s.T.Z) s.T.m0) (B := CechPic.dual s.T.BD.lb)
      (LB.isLB_linComb hO _ _) (CechPic.isLB_dual hB) hP
    rw [CechPic.cls_lbPow hO, CechPic.cls_dual hB, ← sub_eq_add_neg] at h
    exact h
  have e2 : CechPic.pull ((Φ.C k).π ≫ genι s.T.Z) (CechPic.cls _ hO) =
      toPic (-∑ x : Letter S.Dw, (Φ.C k).gr x.1 x.2) := by
    rw [← CechPic.cls_pull hO _ (pull_isLB hO _), toPic_apply]
    exact ((CechPic.cls_eq_iff _ _).2 (GlobalTheory.T.flag_determinant_iso D A N j S κ s Φ k)).symm
  have e3 : CechPic.pull ((Φ.C k).π ≫ genι s.T.Z) (CechPic.cls _ hB) = toPic (bdPull Φ k) := by
    rw [← CechPic.cls_pull hB _ (pull_isLB hB _), toPic_apply]
    exact ((CechPic.cls_eq_iff _ _).2 (GlobalTheory.T.flag_boundary_iso D A N j S κ s Φ k)).symm
  have e4 : (∑ x : DV.Rt D.what₂.Tau N, (if (x.2 : ℕ) < j then 0 else 2 * s.T.m0 : ℕ) • divOf (Φ.C k) (rootExp S x)) =
      s.T.m0 • ∑ x : DV.Rt D.what₂.Tau N, (if (x.2 : ℕ) < j then 0 else 2 : ℤ) • divOf (Φ.C k) (rootExp S x) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs
    · simp
    · simp only [← natCast_zsmul, smul_smul]
      congr 1
      push_cast
      ring
  have e5 : toPic (∑ x : DV.Rt D.what₂.Tau N, divOf (Φ.C k) (rootExp S x)) = 0 := by
    rw [Fintype.sum_prod_type, map_sum]
    exact Finset.sum_eq_zero fun τ _ => GlobalTheory.T.root_divisor_sum_trivial D A N j S κ s Φ k τ
  rw [e1, map_sub, map_sub, map_nsmul, e2, e3, e4, map_nsmul, GlobalTheory.T.flag_root_divisor_relation D A N j S κ s Φ k, map_add, e5, add_zero]
