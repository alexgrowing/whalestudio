import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k V.rank Y) (gl : GL Y k →* GA D V), (∀ g, (ofSplit q).IsLoc F (gl g) g) → Topology.IsClosedEmbedding gl ∧ gl.range = GlobalTheory.FinPl.grpAt V (· = q.v) ∧ (∀ x : GA D V, ∃! g, x * (gl g)⁻¹ ∈ GlobalTheory.FinPl.grpOff V (· = q.v)) ∧ (∀ g, ∀ y ∈ GlobalTheory.FinPl.grpOff V (· = q.v), gl g * y = y * gl g) ∧ ∀ L : GlobalTheory.FinPl.Lat V, IsSelfDualC V L → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V L (· = q.v)) → ∀ g, g ∈ KO k Y ↔ GlobalTheory.FinPl.InK V L (· = q.v) (gl g) := by
  first | exact @GlobalTheory.LocGl.local_group | exact GlobalTheory.LocGl.local_group | (intros; apply GlobalTheory.LocGl.local_group <;> assumption)
