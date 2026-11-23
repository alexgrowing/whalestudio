import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowFourierOntoAndSpanTransformedLastRow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_fourier_onto_and_span_transformed_last_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n Z : Type) [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z], (∀ b : SB (Matrix Unit n k), ∃ c : SB (Matrix n Unit k), ∀ η, b.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ())) ∧ ∀ Ξ₂ : SB (Matrix (Z ⊕ Unit) n k), ∃ (N : ℕ) (a : Fin N → SB (Matrix Z n k)) (c : Fin N → SB (Matrix n Unit k)) (g : Fin N → SB (Matrix (Z ⊕ Unit) n k)), (∀ i x, (g i).1 x = (a i).1 x.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => (c i).1 (Matrix.of fun r _ => y r)) (x (Sum.inr ()))) ∧ Ξ₂ = ∑ i, g i := by
  first | exact @GlobalTheory.LocMod.LastRow.transform_onto_and_span_lastRow | exact GlobalTheory.LocMod.LastRow.transform_onto_and_span_lastRow | (intros; apply GlobalTheory.LocMod.LastRow.transform_onto_and_span_lastRow <;> assumption)
