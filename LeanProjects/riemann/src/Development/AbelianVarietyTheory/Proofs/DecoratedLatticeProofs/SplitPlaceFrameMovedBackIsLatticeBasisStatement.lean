import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameMovedBackIsLatticeBasis
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceFrame_movedBack_isLatticeBasis : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V) (L N : GlobalTheory.FinPl.Lat V) (P : GlobalTheory.FinPl.Pl D → Prop), P q.v → IsSelfDualC V L → IsSelfDualC V N → GlobalTheory.FinPl.Moves V g L N P → ∀ (Y : Type) [Fintype Y] (β β' : Matrix (Fin V.rank) Y k), β = (Formalism.L2.Theta.mt V g).map q.pr * β' → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V N (· = q.v)) → ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((β' *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V L (· = q.v) := by
  first | exact @GlobalTheory.FinPl.FrameBack.frame_back | exact GlobalTheory.FinPl.FrameBack.frame_back | (intros; apply GlobalTheory.FinPl.FrameBack.frame_back <;> assumption)
