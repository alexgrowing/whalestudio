import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobalRowsOfSizeParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NodesOfSizeData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypothesesOfGlobalRowsAndNodesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceLowerBoundAllMembersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceUpperBoundAllMembersStatement
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.HypAt

theorem del_lo {x eps k f CD cD : ℝ} (hx : 1 ≤ x) (he : eps ≤ 1) (hk0 : 0 ≤ f) (hfk : f ≤ k)
    (hk : k ≤ x ^ (5 : ℝ)) (hCD : 0 ≤ CD) (hc : 11 * CD ≤ cD) :
    (k * f * x ^ eps) ^ CD ≤ ((⌈x ^ cD⌉₊ : ℕ) : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hk0' : 0 ≤ k := le_trans hk0 hfk
  have h1 : x ^ eps ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx he
  have h2 : k * f ≤ x ^ (5 : ℝ) * x ^ (5 : ℝ) := mul_le_mul hk (le_trans hfk hk) hk0 (by positivity)
  have h3 : k * f * x ^ eps ≤ x ^ (11 : ℝ) := by
    have : x ^ (11 : ℝ) = x ^ (5 : ℝ) * x ^ (5 : ℝ) * x ^ (1 : ℝ) := by
      rw [← Real.rpow_add' hx0 (by norm_num), ← Real.rpow_add' hx0 (by norm_num)]; norm_num
    rw [this]
    exact mul_le_mul h2 h1 (by positivity) (by positivity)
  calc (k * f * x ^ eps) ^ CD ≤ (x ^ (11 : ℝ)) ^ CD := Real.rpow_le_rpow (by positivity) h3 hCD
    _ = x ^ (11 * CD) := by rw [← Real.rpow_mul hx0]
    _ ≤ x ^ cD := Real.rpow_le_rpow_of_exponent_le hx hc
    _ ≤ _ := Nat.le_ceil _

theorem evP_hypL (A B : Formalism.MainNotions.Inhab.FC → ℝ) : EvP fun κ K => ∀ β : BPt K,
    (∀ u : β.D.what₂.Word, β.O.L.sc.b ^ ((1 / 2 : ℝ) * (β.D.R.m : ℝ)) ≤ Formalism.MainNotions.S.Tr β.D u ∧
      Formalism.MainNotions.S.Tr β.D u ≤ β.O.L.sc.b ^ (κ.C.CTu * (β.D.R.m : ℝ))) →
    GlobalTheory.Core.Deg.HypL β.D β.O.L.sc.L (max (A κ.C) (8 * κ.C.CGam)) (max (B κ.C) 40) (κ.C.P.CYL + 1) (1 / 4) 3 (1 / 2)
      κ.C.CTu := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  have hCD3 : (3 : ℝ) ≤ max (B C) 40 := le_trans (by norm_num) (le_max_right _ _)
  have hCD0 : (0 : ℝ) < max (B C) 40 := by linarith
  refine ⟨max c1 (11 * max (B C) 40), fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD (le_trans (le_max_left _ _) hcD)
  refine ⟨c2, fun ch hch _ => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch hch
  obtain ⟨x2, hNo⟩ := GlobalTheory.Diag.PG.NodeParameters.nodes_of_parameters eps he he52
  obtain ⟨x3, hH⟩ := GlobalTheory.T.hypotheses_of_global_rows_and_nodes eps (max (B C) 40) he he52 hCD3 (max (A C) (8 * C.CGam)) (max (B C) 40)
    (C.P.CYL + 1) hCD0 le_rfl
  refine ⟨max (max x1 x2) (max x3 ((max 2 (5 / (eps / 100))) ^ (eps / 100)⁻¹)), fun K hK hx β hW => ?_⟩
  obtain ⟨hC, hcD', hch', heps, -⟩ := hK
  have hsc : β.O.L.sc = K.s := β.sc
  have hx' : max (max x1 x2) (max x3 ((max 2 (5 / (eps / 100))) ^ (eps / 100)⁻¹)) ≤ β.O.L.sc.x := by rw [hsc]; exact hx
  have hse : β.O.L.sc.eps = eps := by rw [hsc]; exact heps
  have hv : Val C cD ch β.O.L := by
    rw [show C = K.C from hC.symm, show cD = K.cD from hcD'.symm, show ch = K.ch from hch'.symm]
    exact β.p.pt_val β.val
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ hse (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx') hv
    (GlobalTheory.Plug.hostArith_bpt β)
  have hx1 : 1 < β.O.L.sc.x := β.O.L.sc.one_lt_alt
  have hX : max 2 (5 / (eps / 100)) ≤ S.XX β.O.L := by
    unfold S.XX szTh
    rw [hse]
    have h0 : (0 : ℝ) ≤ max 2 (5 / (eps / 100)) := le_trans (by norm_num) (le_max_left _ _)
    have hp : 0 < eps / 100 := by positivity
    have hyP : (max 2 (5 / (eps / 100))) ^ (eps / 100)⁻¹ ≤ β.O.L.sc.x :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx'
    have := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hyP hp.le
    rwa [Real.rpow_inv_rpow h0 hp.ne'] at this
  have G0 := GlobalTheory.Diag.PG.Model0.globalRows_of_sizeData β.O.L N.params N.sizes ((le_max_left _ _).trans hX)
    (by unfold szTh; rw [hse]; exact (le_max_right _ _).trans hX) N.params.CCount N.params.CCount_pos le_rfl
  have e2 : N.params.CYL = C.P.CYL := congrArg (fun l : List ℝ => l.getD 19 0) N.params_K
  rw [hse, e2] at G0
  have hDel : ((β.D.s.Del : ℚ) : ℝ) = ((⌈β.O.L.sc.x ^ cD⌉₊ : ℕ) : ℝ) := by
    rw [hv.Del_eq]; unfold Delv; push_cast; rfl
  have hDl : ((β.D.R.k : ℝ) * (β.D.R.f : ℝ) * β.O.L.sc.x ^ eps) ^ max (B C) 40 ≤ ((β.D.s.Del : ℚ) : ℝ) := by
    rw [hDel]
    exact del_lo hx1.le (by linarith) (by positivity) G0.nums.fk G0.nums.k_hi hCD0.le
      (le_trans (le_max_right _ _) hcD)
  have G : GlobalTheory.Diag.PG.Glob0 β.D β.O.L.sc.x eps (max (B C) 40) (C.P.CYL + 1) :=
    ⟨⟨G0.nums.m_lo, G0.nums.mf, G0.nums.fk, G0.nums.k_lo, G0.nums.k_hi, G0.nums.lrd_lo, G0.nums.lrd_hi, hDl,
      G0.nums.Del_hi⟩, G0.g_win, G0.gap, G0.cloud, G0.off, G0.rd_lo⟩
  have hNd := hNo β.D β.O.L N.params N.sizes hse (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx')
  have hL : β.O.L.sc.L = β.O.L.sc.x ^ eps := by rw [← hse]; rfl
  have h8 : 8 * β.O.L.CGam ≤ max (A C) (8 * C.CGam) := by rw [N.CGam_eq]; exact le_max_right _ _
  exact GlobalTheory.Core.Deg.hypL_of (hH β.O.L.sc.x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx') β.D β.O.L
    (1 / 2) C.CTu hL h8 G hNd hW)

theorem hypL_at_points : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL) (A B : Formalism.MainNotions.Inhab.FC → ℝ), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun κ D O _ _ => GlobalTheory.Core.Deg.HypL D O.L.sc.L (max (A κ.C) (8 * κ.C.CGam)) (max (B κ.C) 40) (κ.C.P.CYL + 1) (1 / 4) 3 (1 / 2) κ.C.CTu) := by
  intro hL p A B
  exact (EvP.and (RowE.and (GlobalTheory.T.trace_lower_bound_all_members hL p) (GlobalTheory.T.trace_upper_bound_all_members hL p)) (evP_hypL A B)).mono fun _ _ _ H β hq c b hl =>
    H.2 β fun u => ⟨(H.1 β hq c b hl).1 u, (H.1 β hq c b hl).2 u⟩

end GlobalTheory.Core.HypAt
