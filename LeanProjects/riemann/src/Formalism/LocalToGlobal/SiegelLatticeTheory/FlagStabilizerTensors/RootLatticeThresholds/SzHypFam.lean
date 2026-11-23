import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypOf
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyCriticalLevelLowerBound
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DegreeRatioFormulaStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CriticalLevelLowOfRefined
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

namespace Formalism.L2.SG.Pf.SzHypFam

variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in

theorem midVolumeChain_of_standingHypotheses {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT ep0 CV : ℝ} (hT : Ties D)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCL : 1 ≤ Cl * large₂.sc.L) (he : 0 ≤ ep0) (hCV : 0 ≤ CV) :
    LocalBesselAndTopKernel.MidVolumeChain D large₂ ep0 CV := by
  intro τ
  rw [Formalism.L2.SG.Pf.SzHypFD.vv_eq_vand hT hH hCL τ]
  have h0 : 0 ≤ vand (lamSH D.R (D.hc τ)) := Formalism.MainNotions.BridgeLemma.szh_vand_nonneg _ (Formalism.MainNotions.BridgeLemma.szh_anti hH τ)
  have hL := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hx : 0 ≤ CV * D.R.k * D.R.m * large₂.sc.L := by positivity
  have h1 : 1 ≤ Real.exp (CV * D.R.k * D.R.m * large₂.sc.L) := Real.one_le_exp hx
  constructor
  · nlinarith
  · nlinarith

variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in

theorem familyTopBound_of_one_le_sCl {eps : ℝ} (Fm : FamP eps) (h1 : 1 ≤ sCl Fm) (C0 Cg cb Cu cT CT ep0 CV : ℝ) (he : 0 ≤ ep0)
    (hCV : 0 ≤ CV) : LocalBesselAndTopKernel.FamilyTopBound Fm C0 Cg cb Cu cT CT ep0 CV := by
  refine ⟨0, fun x _ i hh => ?_⟩
  have hL := Formalism.MainNotions.BridgeLemma.one_le_L (Fm.L x i)
  exact midVolumeChain_of_standingHypotheses (Fm.ties x i) hh.2.1 (by nlinarith) he hCV

variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in

theorem localSplitExponents_of_forty_le_sCl {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) (C0 Cg cb Cu cT CT : ℝ) :
    LocalBesselAndTopKernel.LocalSplitExponents Fm C0 Cg cb Cu cT CT 1 :=
  Formalism.MainNotions.BridgeLemma.family_critical_level_lower_bound Fm (ep0 := 1 / 3) (CV := 0) h40 (by norm_num) le_rfl
    (familyTopBound_of_one_le_sCl Fm (by linarith) C0 Cg cb Cu cT CT (1 / 3) 0 (by norm_num) le_rfl)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem secondSizeStatement_of_famP {eps : ℝ} (Fm : FamP eps) : LocalBesselAndTopKernel.SecondSizeStatement Fm := fun x i =>
  Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified Formalism.HermitianLattices.Ext.L3.siegelMassRatio (Fm.D x i)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem familyBesselBoundFirstPart_of_ranksF {eps : ℝ} (Fm : FamP eps) {C0 Cg cb Cu cT CT : ℝ} (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) :
    LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT :=
  Formalism.MainNotions.BridgeLemma.level_formula_family Fm C0 Cg cb Cu cT CT (secondSizeStatement_of_famP Fm)
    (Formalism.MainNotions.BridgeLemma.mass_two_bound_family_holds Fm) hR

variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem tFrame_of_ranks {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) {C0 Cg cb Cu cT CT : ℝ}
    (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) : PX.TFrame Fm Cg cb Cu cT CT C0 :=
  Formalism.MainNotions.BridgeLemma.level_frame_of_sizes Fm Cg cb Cu cT CT C0 1 (by linarith) (familyBesselBoundFirstPart_of_ranksF Fm hR)
    (localSplitExponents_of_forty_le_sCl Fm h40 C0 Cg cb Cu cT CT)

def aSz (C0 : ℝ) : List ℝ → ℝ := fun _ => Real.exp (3 / 4) * (C0 * Real.exp 1)

theorem one_le_aSz {C0 : ℝ} (h1 : 1 ≤ C0) (l : List ℝ) : 1 ≤ aSz C0 l := by
  unfold aSz
  have a := Real.one_le_exp (show (0 : ℝ) ≤ 3 / 4 by norm_num)
  have b := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
  have c : 1 ≤ C0 * Real.exp 1 := by nlinarith
  nlinarith

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem sizes3b_of_ranks {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) {C0 Cg cb Cu cT CT : ℝ} (h1 : 1 ≤ C0)
    (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) :
    OwnEv Fm fun C' Cl x i => LocalBesselAndTopKernel.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT →
      Formalism.MainNotions.Sizes3b (Fm.D x i) (aSz C0 Fm.cOut) := by
  have hb : LocalBesselAndTopKernel.TheoremThreePassage Fm C0 Cg cb Cu cT CT (Real.exp (3 / 4)) := Formalism.MainNotions.BridgeLemma.family_critical_level_ratio Fm h40 le_rfl
  have hc : LocalBesselAndTopKernel.FamilyLowestKType Fm C0 Cg cb Cu cT CT (Real.exp (3 / 4) * (C0 * Real.exp 1)) :=
    Formalism.MainNotions.BridgeLemma.family_level_ratio_bound Fm C0 Cg cb Cu cT CT _ _ le_rfl (familyBesselBoundFirstPart_of_ranksF Fm hR) hb
  have hA := one_le_aSz h1 Fm.cOut
  have hC1 : Real.exp (3 / 4) ≤ aSz C0 Fm.cOut := by
    unfold aSz
    have b := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
    have c : 1 ≤ C0 * Real.exp 1 := by nlinarith
    have := Real.exp_pos (3 / 4)
    nlinarith
  exact Formalism.MainNotions.sizes3bF Fm C0 Cg cb Cu cT CT _ _ _ (Real.exp_pos _).le hC1 le_rfl hb hc

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in

theorem szRowsAt_of_ties {D : D7} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hD : StandingNumericalData D C0)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCL : 1 ≤ Cl * large₂.sc.L) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) :
    Formalism.L2.SG.Pf.SzHypOf.SzRowsAt D :=
  ⟨Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified Formalism.HermitianLattices.Ext.L3.siegelMassRatio D, hR, Formalism.MainNotions.BridgeLemma.sza_spl_of_data hD,
    fun τ => Formalism.L2.SG.Pf.SzHypFD.fdl_of_ties hT hH hCL τ⟩

section Rows

open Formalism.L2.SG.ThmSOwn

variable (C0 : ℝ)

def RanksRow (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => PX.RanksF Fm C0 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu

variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem hTF_of_ranks {𝒞 : FamClass} (hRk : RanksRow C0 𝒞) :
    Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 :=
  closed_with hRk (fun _ => 0) (fun _ => 40) fun Fm _ _ hR _ _ h2 => tFrame_of_ranks Fm h2 hR

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem hA_of_ranks {𝒞 : FamClass} (h1 : 1 ≤ C0) (hRk : RanksRow C0 𝒞) :
    Closed 𝒞 fun Fm _ => 1 ≤ aSz C0 Fm.cOut ∧ OwnEv Fm fun C' Cl x i =>
      AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
        Formalism.MainNotions.Sizes3b (Fm.D x i) (aSz C0 Fm.cOut) :=
  closed_with hRk (fun _ => 0) (fun _ => 40) fun Fm _ _ hR _ _ h2 =>
    ⟨one_le_aSz h1 _, sizes3b_of_ranks Fm h2 h1 hR⟩

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in

theorem hRw_of_ranks {𝒞 : FamClass} (hRk : RanksRow C0 𝒞) :
    Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
        Formalism.L2.SG.Pf.SzHypOf.SzRowsAt (Fm.D x i) :=
  closed_with hRk (fun _ => 0) (fun _ => 1) fun Fm _ _ hR _ _ h2 => by
    obtain ⟨x0, H⟩ := hR
    refine ⟨x0, fun x hx i hh => ?_⟩
    have hL := Formalism.MainNotions.BridgeLemma.one_le_L (Fm.L x i)
    have h2' : 1 ≤ sCl Fm := h2
    exact szRowsAt_of_ties (Fm.ties x i) hh.1 hh.2.1 (by nlinarith) (H x hx i hh)

end Rows

end Formalism.L2.SG.Pf.SzHypFam
