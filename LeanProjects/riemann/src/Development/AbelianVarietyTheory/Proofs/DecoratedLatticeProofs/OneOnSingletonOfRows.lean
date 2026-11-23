import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNml
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpUnifPOf
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedUniformRotatedOfExpansion
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Diag

theorem mR_eq_m (D : D7) : Formalism.L2.SG.RowsConc.mR D = (D.R.m : ℝ) := by
  have h : 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨j, hj⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  unfold Formalism.L2.SG.RowsConc.mR
  rw [h]

theorem log_b_eq (D : D7) (large₂ : SizeData₂ D) : Real.log large₂.sc.b = large₂.sc.L := by
  unfold Formalism.BasicNotions.Scale.b
  exact Real.log_exp _

theorem gamB_eq_gamL (D : D7) (large₂ : SizeData₂ D) (C : ℝ) : gamB D large₂ C = gamL D large₂.sc.L C := by
  unfold gamB gamL
  rw [mR_eq_m, log_b_eq]

theorem epsNG_le_gamL (D : D7) (large₂ : SizeData₂ D) (C : ℝ) : epsNG D large₂ C ≤ gamL D large₂.sc.L C := by
  unfold epsNG
  have h1 : ((2 : ℝ) ^ (D.R.k - 2 * D.R.rS - 5))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h2 : Real.exp (C * Formalism.L2.SG.RowsConc.mR D ^ 5 * D.R.f * Real.log large₂.sc.b) = gamL D large₂.sc.L C := by
    unfold gamL
    rw [mR_eq_m, log_b_eq]
  rw [h2]
  exact mul_le_of_le_one_left (Real.exp_pos _).le h1

theorem oneOn_singleton_of_rows :
    (RowGen1P → ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true) ∧ (GlobalTheory.NGRow.RowNGP → ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} false) := by
  constructor
  · intro hG c Cg cb Cu cT CT hcb hcT
    obtain ⟨CB, hCB, C'₀, Cl₀, H⟩ := hG Cg cb Cu cT CT c hcb hcT
    refine ⟨CB, hCB, max (max C'₀ Cl₀) 3, ?_⟩
    intro C0 hC0 C' Cl h1 h2 D large₂ X Y u hT hH hC ha
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    have a1 : C'₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
    have b1 : Cl₀ ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
    have b3 : (2 : ℝ) < Cl := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) h2)
    have hs : Formalism.MainNotions.S.Cnt.Stand D u u := Formalism.MainNotions.Stand_of D large₂ C' Cl Cg cb Cu cT CT C0 hH.2.1 hH.1 b3 u u
    have r := H C' Cl a1 b1 D large₂ X Y u hT hH hs hC ha
    unfold GeneratorBoundAt at r
    rw [gamB_eq_gamL] at r
    rw [if_pos rfl]
    exact r
  · intro hN c Cg cb Cu cT CT hcb hcT
    obtain ⟨C4, hC4, C'₀, Cl₀, H⟩ := hN Cg cb Cu cT CT c hcb hcT
    refine ⟨C4, hC4, max (max C'₀ Cl₀) 3, ?_⟩
    intro C0 hC0 C' Cl h1 h2 D large₂ X Y u hT hH hC ha
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    have a1 : C'₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
    have b1 : Cl₀ ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
    have b3 : (2 : ℝ) < Cl := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) h2)
    have hs : Formalism.MainNotions.S.Cnt.Stand D u u := Formalism.MainNotions.Stand_of D large₂ C' Cl Cg cb Cu cT CT C0 hH.2.1 hH.1 b3 u u
    have r : (Y.tO u u).pairSum ((Y.tO u u).one (Y.tO u u).ngSet) ≤ epsNG D large₂ C4 * ddC X Y u u :=
      H C' Cl a1 b1 D large₂ X Y u u hT hH hs hC ha
    rw [if_neg Bool.false_ne_true]
    exact r.trans (mul_le_mul_of_nonneg_right (epsNG_le_gamL D large₂ C4) (Formalism.L2.SG.RowsConc.dd_nonneg hC u u))

end GlobalTheory.Core.Diag
