import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.RunsAlong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.XLeZBaseOfPowLeN
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HostSzOfSizes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsParametersOver

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Plug

theorem hostArith_of_over {K : Ctx} {B : Pre} (h : K.Over B) : HostArith B.host := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  exact ⟨K.ok.arith.1, K.ok.arith.2.1, K.ok.arith.2.2.1, (Pre.ofCh K.P K.Lv sp hT hY hA hV hz).level_split⟩

theorem hostArith_bpt {K : Ctx} (β : BPt K) : HostArith β.D.host := hostArith_of_over β.c.isOver

theorem eventually_hostSize_and_numAt : EvP fun _ K => ∀ β : BPt K, GlobalTheory.FieldSize.HostSz β.D.host β.O.L.sc.L ∧
    ∀ C, FieldTies β.D C → NumAtL β.O.L K.s.x := by
  refine EvP.of_ev ⟨1, one_pos, fun eps C8 he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, hN⟩ := hN ch hch
  refine ⟨max x0 (max (C.T.CP ^ 20) ((10 : ℝ) ^ 60)), fun K h1 h2 h3 h4 hx β => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hy0, hyP, hy60⟩ := hx
  have hsc : β.O.L.sc = K.s := β.sc
  have hsx : β.O.L.sc.x = K.s.x := by rw [hsc]
  have hse : β.O.L.sc.eps = eps := by rw [hsc, h4]
  have hv : Val C cD ch β.O.L := by
    rw [← h1, ← h2, ← h3]
    exact β.p.pt_val β.val
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ hse (hy0.trans hsx.ge) hv (hostArith_bpt β)
  have hCP : N.parT.CP = C.T.CP := (List.cons.inj N.parT_K).1
  have hg : ∀ j, Real.log (β.D.host.g j) ≤ 9 * β.O.L.sc.L + 1 := by
    intro j
    have hlo : 0 < ((β.D.host.g j : ℕ) : ℝ) := by
      exact_mod_cast (β.D.host.g_prime j).pos
    have := (Real.log_le_iff_le_exp hlo).2 (N.g_le j)
    linarith
  obtain ⟨hH, hS⟩ := GlobalTheory.FieldSize.hostSz_of_sizes β.D β.O.L N.params N.parT N.sizes hg (hy60.trans hsx.ge)
  refine ⟨hH, fun Cf hT => ⟨β.O.ex.kap_def, ⟨N.params, N.parT, N.sizes, N.CnW_eq.trans hStd.1.2.2.2.2.2.2.2.1, hg, ?_, ?_,
    hsx.ge⟩, hS (hT.small _ hH)⟩⟩
  · rw [hCP]; exact hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hCP]
    exact hyP.trans (hsx.ge.trans (x_le_zBase_of_pow_le_n β.O.L N.win.1.1))

end GlobalTheory.Plug
