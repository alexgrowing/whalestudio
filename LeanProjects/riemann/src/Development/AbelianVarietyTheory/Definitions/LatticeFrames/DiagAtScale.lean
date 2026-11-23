import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams

noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2
namespace GlobalTheory.Core.Diag

def RowNGEq : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ C4 : ℝ, 0 ≤ C4 ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.MainNotions.S.Cnt.Stand D u u → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).RowNG (epsNG D large₂ C4) (ddC X Y u u)

def RowMainEq : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, 0 < cb → 0 < cT → ∃ CB : ℝ, 0 ≤ CB ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).RowMain (gamB D large₂ CB) (ddC X Y u u)

def RowLoopEq : Prop :=
  ∀ Cg cb Cw cT CT C0 A CG : ℝ, 0 < cb → 0 < cT → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (_ : SIso D.s (sOf hF)) (u : D.what₂.Word),
      Formalism.BasicNotions.Ties D → Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D → large₂.CGam = CG →
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).RowBig (epsL D) (ddC X Y u u) ∧ (Y.tO u u).RowNotScalar (epsL D) (ddC X Y u u)

def RowKppEq : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv →
      Summable ((Y.tO u u).degSet.indicator (fun t => ‖(Y.tO u u).op t‖)) ∧
      Formalism.L2.SG.RowsOther.KppDiag (Y.tO u u) (duC X Y u) D.R.k D.R.f

def RowDiagEq : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, 0 < cb → 0 < cT → ∃ CG₀ : ℝ, ∀ CG : ℝ, CG₀ ≤ CG →
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (_ : SIso D.s (sOf hF)) (u : D.what₂.Word),
      Formalism.BasicNotions.Ties D → Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D →
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoParameterConditions D large₂ Cl Cg CT →
      ConcTie X Y → (Y.tO u u).AbsConv → large₂.CGam = CG →
      Formalism.L2.SG.RowsOther.DiagRow (Y.tO u u) (oneC X Y u) (D.mem u).A.GamP (ddC X Y u u)

def TrueS (D : D7) : Prop :=
  Formalism.BasicNotions.Ties D ∧ Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D ∧ Formalism.L2.SG.Pf.LocCP.LocTied D ∧ Nonempty (Formalism.L2.SG.SpectralTiesReal.STies D)

def TFrameP : Prop :=
  ∀ Cg cb Cu cT CT C0 CG : ℝ, 0 < cb → 0 < cT → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), Formalism.BasicNotions.Ties D → Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D → large₂.CGam = CG →
      Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1 → AdmissibleBoundsFromSource.hyp D large₂ C0 C' Cl Cg cb Cu cT CT → TFrameAt D

def e0 (D : D7) (C0 : ℝ) : ℝ := 2 * C0 / AdmissibleBoundsFromSource.Gam D + 2 * AdmissibleBoundsFromSource.xK D

def AtLed (Q : D7 → ℝ → Prop) : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CG₀ : ℝ, ∀ CG : ℝ, CG₀ ≤ CG →
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), TrueS D → TFrameAt D → large₂.CGam = CG → AdmissibleBoundsFromSource.hyp D large₂ C0 C' Cl Cg cb Cu cT CT → Q D C0

def ClausesLed : Prop := AtLed fun D _ => Formalism.L2.SG.ThmSOwn.ClKppDiag D ∧ Formalism.L2.SG.ThmSOwn.ClDiag D

def DiagLed : Prop := AtLed fun D C0 => ∀ u, GlobalTheory.Core.Rk.DiagS D u (e0 D C0)

def HasLed (D : D7) (L CG : ℝ) : Prop := ∃ large₂ : SizeData₂ D, large₂.sc.L = L ∧ large₂.CGam = CG

def DiagAtScale : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, 0 < cb → 0 < cT → 1 ≤ C0 → ∃ CG₀ : ℝ, ∀ CG : ℝ, CG₀ ≤ CG →
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ), TrueS D → TFrameAt D → HasLed D L CG → GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT → StandingNumericalData D C0 →
      ∀ u, GlobalTheory.Core.Rk.DiagS D u (e0 D C0)

def HD (D : D7) (L C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT ∧ GlobalTheory.Core.Deg.DataNW D ∧ TFrameAt D

def gamL (D : D7) (L C : ℝ) : ℝ := Real.exp (C * (D.R.m : ℝ) ^ 5 * D.R.f * L)

def SDiagAt (D : D7) (u : D.what₂.Word) (Γ c : ℝ) : Prop :=
  GlobalTheory.Core.Rk.hsDev D u ≤
    4 * ((Γ + 1) * (D.duS u : ℝ) ^ 2 / D.what₂.Dstar + (D.duS u : ℝ) * Real.exp (-(c * D.R.k * D.R.f * Real.log D.R.k))) +
      2 * (D.duS u : ℝ) * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))

def SDiag (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ), TrueS D → HD D L C' Cl Cg cb Cu cT CT → ∀ u, SDiagAt D u (gamL D L CD) c

def SDiagLed (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), TrueS D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → GlobalTheory.Core.Deg.DataNW D → TFrameAt D →
      ∀ u, SDiagAt D u (gamL D large₂.sc.L CD) c

def SDiagWin (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), TrueS D → Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → TFrameAt D →
      ∀ u, SDiagAt D u (gamL D large₂.sc.L CD) c

def SDiagHas (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ), TrueS D → (∃ large₂ : SizeData₂ D, large₂.sc.L = L) → 8 * Real.log (AdmissibleBoundsFromSource.Gam D) ≤ D.R.k →
      HD D L C' Cl Cg cb Cu cT CT → ∀ u, SDiagAt D u (gamL D L CD) c

def OneLed (gen : Bool) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C : ℝ, 0 ≤ C ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → GlobalTheory.Core.Deg.DataNW D → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).pairSum ((Y.tO u u).one (if gen then (Y.tO u u).genSet else (Y.tO u u).ngSet)) ≤
        gamL D large₂.sc.L C * ddC X Y u u
end GlobalTheory.Core.Diag
