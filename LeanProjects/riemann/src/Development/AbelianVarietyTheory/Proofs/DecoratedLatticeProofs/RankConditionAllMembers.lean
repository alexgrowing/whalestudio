import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Formalism.PeriodIntegrals.WeylProd
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylProd
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LwRankTies
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassNumberAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstTypePrimeLargeOfRecord
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.MemberCount

theorem rankMu_of_cols (D : D7) (Lv : LevelData D) (C : Formalism.L2.Forms.ColsTiedSym D) (hDu : StandardLattice.FactDuStar D)
    (u : D.what₂.Word) : GlobalTheory.Core.Rk.RankMu D u := by
  have h4 := Formalism.MainNotions.StandardLattice.HarishChandraReduction.rankFormula_of_classNumber D Lv (GlobalTheory.ColClassNumber.classNumber_all D Lv)
  have hr := h4 (GlobalTheory.first_type_prime_large_of_record D) (Formalism.MainNotions.Ext.Lw.splitsF_g_all D) u
    (Formalism.MainNotions.Ext.Lw.splitsF_T_all D u) (Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u)
  have hfin : Module.finrank ℂ (D.s.Cu u) = Module.finrank ℂ (D.mem u).A.Mu0 := (D.s_Cu u).finrank_eq
  unfold GlobalTheory.Core.Rk.RankMu GlobalTheory.Core.Rk.d0
  rw [hfin, hDu u]
  exact hr

theorem rankMu_of_bundle {D : D7} {O : Obj D} {c : ℝ} (b : GlobalTheory.Fc.Bundle D O c) (u : D.what₂.Word) :
    GlobalTheory.Core.Rk.RankMu D u :=
  rankMu_of_cols D O.ex.lev b.R.T.toTiedDataS.cols O.ex.duStar_def u

theorem member_rankMu : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => ∀ u, GlobalTheory.Core.Rk.RankMu D u) :=
  fun _ _ => RowE.of_all fun _ _ _ _ b _ _ _ u => rankMu_of_bundle b u

end GlobalTheory.Fam.MemberCount
