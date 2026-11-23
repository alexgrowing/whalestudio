import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdmissibleRanksAllMembersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegreeHypothesisAllMembersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataNonvanishingAllMembersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeFrameAllMembersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RankConditionAllMembersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LargeGapAllMembersStatement
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.MemberSizes

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL)

theorem ties_at : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => Formalism.BasicNotions.Ties D) :=
  RowE.of_all fun _ _ β _ _ _ _ _ => β.p.pt.xa.ties

theorem scale_at (H : Formalism.MainNotions.Inhab.FC → ℝ) : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun κ _ O _ _ =>
    H κ.C ≤ O.L.sc.L ∧ O.L.CGam = κ.C.CGam ∧ 1 ≤ κ.C.CGam) := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ =>
    ⟨0, fun cD _ => ⟨0, fun ch _ _ => ⟨max 1 (max (H C) 1 ^ eps⁻¹), fun K hK hx β _ c b _ => ?_⟩⟩⟩⟩⟩
  have hG : 1 ≤ C.CGam := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [Inhab.FC.cMid])
  have hs : β.O.L.sc = K.s := β.sc
  have hc : β.O.L.CGam = C.CGam := β.val.CGam_eq.trans (congrArg Inhab.FC.CGam hK.1)
  refine ⟨?_, hc, hG⟩
  show H C ≤ β.O.L.sc.x ^ β.O.L.sc.eps
  rw [hs, hK.2.2.2.1]
  have h1 : 0 ≤ max (H C) 1 := le_trans zero_le_one (le_max_right _ _)
  calc H C ≤ max (H C) 1 := le_max_left _ _
    _ = (max (H C) 1 ^ eps⁻¹) ^ eps := (Real.rpow_inv_rpow h1 he.ne').symm
    _ ≤ K.s.x ^ eps := Real.rpow_le_rpow (Real.rpow_nonneg h1 _) (le_trans (le_max_right _ _) hx) he.le

theorem sizes (F G H : ℝ → ℝ → ℝ) : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D O _ _ =>
    ∃ C' Cl Cg CT : ℝ, F Cg CT ≤ C' ∧ G Cg CT ≤ Cl ∧ H Cg CT ≤ O.L.sc.L ∧
      GlobalTheory.Core.Rk.HD D O.L.sc.L C' Cl Cg (1 / 4) 3 (1 / 2) CT ∧ GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D O.L.sc.L C' ∧
      (∀ u, GlobalTheory.Core.Rk.RankMu D u) ∧ GlobalTheory.Core.Rk.BigGap D ∧ 1 ≤ D.R.rS) := by
  have h := (((((((ties_at hL p).and (GlobalTheory.T.admissible_ranks_all_members hL p)).and (GlobalTheory.T.degree_hypothesis_all_members hL p (fun C => F (C.P.CYL + 1) C.CTu) (fun C => G (C.P.CYL + 1) C.CTu))).and (GlobalTheory.T.data_nonvanishing_all_members hL p)).and (GlobalTheory.T.type_frame_all_members hL p)).and (GlobalTheory.T.rank_condition_all_members hL p)).and (GlobalTheory.T.large_gap_all_members hL p)).and (scale_at hL p (fun C => H (C.P.CYL + 1) C.CTu))
  refine RowE.imp h ?_
  intro κ K β c b _ _ _ H0
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8, h9, h10⟩ := H0
  have hm : max (G (κ.C.P.CYL + 1) κ.C.CTu) 40 ≤ (β.D.R.m : ℝ) :=
    h3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨max (F (κ.C.P.CYL + 1) κ.C.CTu) (8 * κ.C.CGam), max (G (κ.C.P.CYL + 1) κ.C.CTu) 40, κ.C.P.CYL + 1, κ.C.CTu,
    le_max_left _ _, le_max_left _ _, h8, ⟨h1, h2, h3, h4, h5⟩, ⟨β.O.L, rfl, h9 ▸ le_max_right _ _, h9 ▸ h10⟩, h6, h7, ?_⟩
  have h40 : (40 : ℝ) ≤ β.D.R.m := le_trans (le_max_right _ _) hm
  have : 40 ≤ β.D.R.m := by exact_mod_cast h40
  show 1 ≤ β.D.R.m / 2 - 1
  omega

theorem member_sizes : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL) (F G H : ℝ → ℝ → ℝ),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D O _ _ => ∃ C' Cl Cg CT : ℝ, F Cg CT ≤ C' ∧ G Cg CT ≤ Cl ∧
      H Cg CT ≤ O.L.sc.L ∧ GlobalTheory.Core.Rk.HD D O.L.sc.L C' Cl Cg (1 / 4) 3 (1 / 2) CT ∧ GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D O.L.sc.L C' ∧
      (∀ u, GlobalTheory.Core.Rk.RankMu D u) ∧ GlobalTheory.Core.Rk.BigGap D ∧ 1 ≤ D.R.rS) :=
  fun hL p F G H => sizes hL p F G H

end GlobalTheory.Fam.MemberSizes

end
