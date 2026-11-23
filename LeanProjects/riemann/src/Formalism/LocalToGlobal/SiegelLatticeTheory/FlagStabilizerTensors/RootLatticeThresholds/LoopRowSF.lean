import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopRowSB
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopLocPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsFinal Formalism.FourierDecayAlt
  Formalism.L2.SG.ThmSOwn

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gap

def GapEv {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ y : ℝ, ∀ x, y ≤ x → ∀ i : Fm.Ix x, Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i)

def CG (𝒞 : FamClass) : FamClass := fun Fm => 𝒞 Fm ∧ GapEv Fm

variable {𝒞 : FamClass} (sel : SSel 𝒞)

def selG : SSel (CG 𝒞) := fun Fm h => sel Fm h.1

def yFG : ∀ {eps : ℝ} (Fm : FamP eps), CG 𝒞 Fm → ℝ := fun _ h => Classical.choose h.2

theorem gap_of {eps : ℝ} {Fm : FamP eps} (h : CG 𝒞 Fm) {x : ℝ} (hx : yFG Fm h ≤ x) (i : Fm.Ix x) :
    Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i) :=
  Classical.choose_spec h.2 x hx i

theorem hyFG (hFX : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC) (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) : YFOK (selG sel) yFG := by
  intro eps Fm hc x hx h0 hy i
  have hg := gap_of hc hy i
  exact ⟨hFX _ _ hg, (hWu _ hg _).1⟩

def CX {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : Formalism.L2.SG.LocWSOf.Choice X 1 :=
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  Classical.choice (Formalism.L2.SG.Pf.choiceExists X 1 one_pos)

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

def BG (hJ : PI.BesselMapUniq.BesselMapUniq) (C1f : List ℝ → ℝ) (hC1 : ∀ l, 0 ≤ C1f l) :
    ∀ {eps : ℝ} (Fm : FamP eps) (hc : CG 𝒞 Fm) x (_ : (Fm.raise (yR (selG sel) yFG Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' (C1f Fm.cOut) :=
  fun Fm hc x hx i u u' => Formalism.L2.SG.Pf.LoopLoc.loopLocDatOf
    (gap_of hc (hyR (selG sel) yFG hx) i) (Fm.ties x i).dsig_tie hJ
    (CX ((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X u)
    (Formalism.L2.SG.Pf.LoopBTheta.normWin_one (Fm.L x i) (hC1 _)) u u'

theorem closed_sub {𝒞' : FamClass} (hs : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → 𝒞 Fm)
    {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (h : Closed 𝒞 P) : Closed 𝒞' P := by
  obtain ⟨e, he, H⟩ := h
  exact ⟨e, he, fun eps h1 h2 => by
    obtain ⟨K, hK⟩ := H eps h1 h2
    exact ⟨K, fun Fm CH hc hL => hK Fm CH (hs Fm hc) hL⟩⟩

variable (C0 : ℝ)

theorem loopRowS_of_sub (hG : Closed 𝒞 fun Fm _ => 𝒞 Fm → GapEv Fm) (h : LoopRowS C0 (CG 𝒞) (selG sel)) :
    LoopRowS C0 𝒞 sel := by
  intro aF
  obtain ⟨e1, he1, H1⟩ := h aF
  obtain ⟨e2, he2, H2⟩ := hG
  refine ⟨min e1 e2, lt_min he1 he2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := H1 eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := H2 eps he (hle.trans (min_le_right _ _))
  refine ⟨K1.sup K2, fun Fm CH hc hL => ?_⟩
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup _ _ CH).1 hL
  intro hc'
  have hg := hK2 Fm CH hc hL2 hc'
  exact hK1 Fm CH ⟨hc', hg⟩ hL1 ⟨hc', hg⟩

end Gap

section PartC

variable {𝒞 : FamClass} (sel : SSel 𝒞)

def RMeasExAll : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF))
    (C : Formalism.L2.SG.LocWSOf.Choice X 1) (u u' : D.what₂.Word),
    (∀ τ, GoodW D τ u u' 1 (Formalism.L2.SG.LocWSOf.locW C u u' τ)) → LoopTerm.RMeasEx hI C u u'

def JFactNAll : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF))
    (C : Formalism.L2.SG.LocWSOf.Choice X 1) (hB : Formalism.L2.SG.LocWSOf.WuBessel C) (u u' : D.what₂.Word),
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D → LoopTerm.JFactN hI C hB u u'

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

def MG (hFX : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC) (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hJ : PI.BesselMapUniq.BesselMapUniq)
    (hRM : RMeasExAll) (hJF : JFactNAll) (hCF : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula) :
    ∀ {eps : ℝ} (Fm : FamP eps) (hc : CG 𝒞 Fm) x (hx : (Fm.raise (yR (selG sel) yFG Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (AtR (selG sel) yFG (hyFG sel hFX hWu) Fm hc x hx i) u u' ((fun _ => 1) Fm.cOut)
        (BG sel hJ (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u') :=
  fun Fm hc x hx i u u' =>
    LoopTerm.loopTermOfN (wOf ((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X)
      (((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).hI
        (hyFG sel hFX hWu Fm hc x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).1)
      (hOf _ _ _ _) (aOfW _ _ _ _ (hyFG sel hFX hWu Fm hc x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).2)
      (hvOfW _ _ _ _ (hyFG sel hFX hWu Fm hc x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).2)
      (Fm.L x i) 1 (CX ((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X u)
      (Formalism.L2.SG.Pf.LoopLoc.wuBessel_of (gap_of hc (hyR (selG sel) yFG hx) i) hJ _) u u'
      (Formalism.L2.SG.Pf.LoopBTheta.normWin_one (Fm.L x i) zero_le_one)
      (BG sel hJ (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u').goodW
      (BG sel hJ (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u').goodS
      (hRM _ _ _ _ _ _ u u' (BG sel hJ (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u').goodW)
      (Formalism.L2.SG.Pf.LoopBPin.pinAll_holds u u') (Formalism.L2.SG.Pf.LoopBPin.covolPos_holds u u')
      (hJF _ _ _ _ _ _ _ u u' (gap_of hc (hyR (selG sel) yFG hx) i))
      (Formalism.L2.SG.Pf.LoopBCovN.covN_pos hCF one_pos _ u u')
      (Formalism.L2.SG.Pf.LoopBCovN.covWinN_sizes hCF _ (Fm.L x i) (Fm.sizes x (raise_lt hx) i) (by norm_num) u u')
      (Formalism.L2.SG.Pf.LoopBTheta.normWin_one (Fm.L x i) zero_le_one)

variable (C0 : ℝ)

end PartC

end Formalism.L2.SG.LoopsTies
