import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeastSplitAuxiliaryPrimeLtScaleBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Mem.AtSize
set_option maxHeartbeats 1000000 in
theorem eventually_sizeRows_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) :
    EvP fun _ K => ∀ β : BPt K, β.Is (IsGoodE p.s) → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows β.O.L := by
  refine EvP.of_ev ⟨1, one_pos, fun eps C8 he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, hN⟩ := hN ch hch
  refine ⟨max x0 (max (44 ^ 4) ((8 : ℝ) ^ (4 / eps))), fun K h1 h2 h3 h4 hx β _ => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hy0, hy44, hy8⟩ := hx
  have hsc : β.O.L.sc = K.s := β.sc
  have hsx : β.O.L.sc.x = K.s.x := by rw [hsc]
  have hse : β.O.L.sc.eps = eps := by rw [hsc, h4]
  have hv : Val C cD ch β.O.L := by
    rw [← h1, ← h2, ← h3]
    exact β.p.pt_val β.val
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ hse (hy0.trans hsx.ge) hv (GlobalTheory.Plug.hostArith_bpt β)
  obtain ⟨C5, c6, Cb, hG⟩ := β.good
  have hq : ((GlobalTheory.ChiGrid.q0 β.D : ℕ) : ℝ) < β.O.L.sc.X' := by
    rw [hsc]
    exact leastSplitAuxiliaryPrime_lt_scaleBound β.c.isOver hG
  refine GlobalTheory.BigTop.Fun.SetAtModel.sizeRows_of N.params N.parT (N.CnW_eq.trans hStd.1.2.2.2.2.2.2.2.1) N.sizes
    N.win.1.1 N.win.2.1.1 N.win.2.1.2 N.win.2.2.1 N.g_le hq N.ccK_top ?_ (by rw [hsx]; exact hy44)
  rw [hsx, hse]
  have e2 : (8 : ℝ) = ((8 : ℝ) ^ (4 / eps)) ^ (eps / 4) := by
    rw [← Real.rpow_mul (by norm_num), show 4 / eps * (eps / 4) = 1 by field_simp, Real.rpow_one]
  rw [e2]
  exact Real.rpow_le_rpow (by positivity) hy8 (by positivity)
end GlobalTheory.Mem.AtSize
end
end
