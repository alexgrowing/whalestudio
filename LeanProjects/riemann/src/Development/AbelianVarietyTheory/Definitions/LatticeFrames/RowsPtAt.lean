import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsFinal
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds

noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2
namespace GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def On (S : Set ℝ) (Q : ∀ {D : D7} {X : HidaSetting D}, Full X → D.what₂.Word → Prop) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (_ : SIso D.s (sOf hF)) (u : D.what₂.Word),
      1 ≤ large₂.CGam → Ties D → LocalBesselAndTopKernel.FamilyMidVolume D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y →
      (Y.tO u u).AbsConv → Q Y u

def Led1 (Q : ∀ {D : D7} {X : HidaSetting D}, Full X → D.what₂.Word → Prop) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ thr : ℝ, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (_ : SIso D.s (sOf hF)) (u : D.what₂.Word),
      1 ≤ large₂.CGam → Ties D → LocalBesselAndTopKernel.FamilyMidVolume D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → DataNW D → ConcTie X Y →
      (Y.tO u u).AbsConv → Q Y u

def AmpAt (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cpr C C2 Ch δ : ℝ) : Prop :=
  UnitaryVolumeMass.stL2prod D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch ∧ UnitaryVolumeMass.stABSprod D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch ∧
    UnitaryVolumeMass.stDEC D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr C Ch δ

def AmpOn (S : Set ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C C2 Ch : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ Cpr δ : ℝ, 0 < δ → ∃ thr : ℝ,
    ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl → ∀ (D : D7) (large₂ : SizeData₂ D), 1 ≤ large₂.CGam → Ties D → LocalBesselAndTopKernel.FamilyMidVolume D →
      TFrameAt D → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 Cpr C C2 Ch δ

def CntAt (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 c3 cH cS c4 : ℝ) : Prop :=
  (∀ C, c3 ≤ C → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 C) ∧ UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH ∧
    UnitaryVolumeMass.stSW D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cS ∧ UnitaryVolumeMass.PartnerCountBound D large₂ u u C' Cl Cg cb Cu cT CT C0 1 c4

def CntOn (S : Set ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, ∃ c3 cH cS c4 thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word), CntAt D large₂ u C' Cl Cg cb Cu cT CT C0 c3 cH cS c4

def CountBoundOn (S : Set ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, ∃ c3 cH thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word),
      (∀ C, c3 ≤ C → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 C) ∧ UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH

def SmallAt (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 δ : ℝ) : Prop :=
  UnitaryVolumeMass.stWeyl D ∧ VanishingOnXAndXPlus.PlaneWaveIsometry D large₂ C' Cl Cg cb Cu cT CT C0 ∧ UnitaryVolumeMass.stTprod D large₂ C' Cl Cg cb Cu cT CT C0 δ ∧
    UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 ∧ (Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt D u)

def SmallOn (S : Set ℝ) : Prop :=
  ∀ Cg cb Cu cT CT δ : ℝ, 0 < cb → 0 < cT → 0 < δ → ∃ thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), Ties D → LocalBesselAndTopKernel.FamilyMidVolume D → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 δ

def TieAt {D : D7} {X : HidaSetting D} {Y : Full X} (hF : FinX Y) (hI : SIso D.s (sOf hF)) (large₂ : SizeData₂ D) (u : D.what₂.Word)
    (T : TermTie D) (Z : LoopTie D large₂ T u u 1) : Prop :=
  Formalism.L2.SG.LoopTieOf.JtPin hF hI T ∧ Formalism.L2.SG.LoopTieOf.WRowPin hF hI T ∧ Formalism.L2.SG.LoopTieOf.FibreCount Y ∧
    BridgeLemma.TermPtsTie T Z ∧ @BridgeLemma.LatticeDeterminantFactorization D T u u ∧ BridgeLemma₂.wordPairEntriesInLattice T u u ∧ BridgeLemma₂.wordPairTermInjective T Z

def TieOn (S : Set ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, ∃ cV thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (u : D.what₂.Word),
      Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y →
      ∃ (T : TermTie D) (Z : LoopTie D large₂ T u u 1), TieAt hF hI large₂ u T Z ∧
        UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV

def RowsPtAt {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) : Prop :=
  (Y.tO u u).RowBig (epsL D) (ddC X Y u u) ∧ (Y.tO u u).RowNotScalar (epsL D) (ddC X Y u u)

def RowsPt : Prop :=
  ∀ Cg cb Cu cT CT C0 CG : ℝ, 0 < cb → 0 < cT → 1 ≤ CG → ∃ thr : ℝ, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (_ : SIso D.s (sOf hF)) (u : D.what₂.Word),
      large₂.CGam = CG → Ties D → LocalBesselAndTopKernel.FamilyMidVolume D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y →
      (Y.tO u u).AbsConv → RowsPtAt Y u
end GlobalTheory.Core.Deg
