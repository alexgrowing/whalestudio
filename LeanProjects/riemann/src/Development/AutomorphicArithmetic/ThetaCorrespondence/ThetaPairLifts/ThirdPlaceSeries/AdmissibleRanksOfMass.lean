import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeFrameAllMembers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypLAtPointsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValSizesAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankMuOfBundleStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.MemberFrame
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL)
theorem admissible_ranks_of_mass_alt : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => LocalBesselAndTopKernel.FamilyMidVolume D) :=
  RowE.of_all fun _ K β _ b _ _ _ =>
    admissible_ranks_of_mass_formula β.D β.O.ex.lev b.R.T.toTiedDataS.cols (Dstar_eq_mass K β.X β.c.isOver β.c.dsig_eq)
theorem three_mul_L_le_m_sub_one_and_cGam : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun κ D O _ _ =>
    3 * O.L.sc.L ≤ (D.R.m : ℝ) - 1 ∧ O.L.CGam = κ.C.CGam) := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb _ _ he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ =>
    ⟨0, fun cD _ => ⟨0, fun ch _ _ => ⟨256, fun K hK hx β _ c b _ => ?_⟩⟩⟩⟩⟩
  have hs : β.O.L.sc = K.s := β.sc
  have hc : β.O.L.CGam = C.CGam := β.val.CGam_eq.trans (congrArg Inhab.FC.CGam hK.1)
  have he' : K.s.eps = eps := hK.2.2.2.1
  exact ⟨three_L_le β.val.ranks (by rw [hs, he']; exact he) (by rw [hs]; exact hx), hc⟩
theorem tFrameAt_at_linked : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p)
    (fun _ D _ _ _ => Formalism.L2.SG.RowsConc.TFrameAt D) := by
  have h := ((((_root_.GlobalTheory.Fam.MemberFrame.admissible_ranks_of_mass_alt hL p).and (_root_.GlobalTheory.T.degHypL_all_linked_good_members hL p (fun _ => 29) (fun _ => 0))).and (_root_.GlobalTheory.T.dataNW_all_linked_good_members hL p)).and
    (_root_.GlobalTheory.T.rankMu_all_linked_members hL p)).and (_root_.GlobalTheory.Fam.MemberFrame.three_mul_L_le_m_sub_one_and_cGam hL p)
  refine RowE.imp h ?_
  intro κ K β c b _ _ _ H0
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, h6⟩ := H0
  have hH : Formalism.MainNotions.S.StandingHypotheses β.D β.O.L (max 29 (8 * κ.C.CGam)) (max 0 40) (κ.C.P.CYL + 1) (1 / 4) 3 (1 / 2) κ.C.CTu :=
    ⟨h6 ▸ le_max_right _ _, h2.2⟩
  exact member_frame_of_standing_hypotheses_window_three β.p.pt.xa.ties h1 ⟨hH, GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu _ h3 h4, by norm_num⟩
    (le_max_left _ _) (le_max_right _ _) h5
theorem tFrameAt_at_linked_of_recT : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.L2.SG.RowsConc.TFrameAt D) :=
  fun hL p => _root_.GlobalTheory.Fam.MemberFrame.tFrameAt_at_linked hL p
end GlobalTheory.Fam.MemberFrame
end
end
