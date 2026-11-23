import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsParabolicDoubleCosetFunctionEqOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parabolicDoubleCosetFunction_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k), (∀ g ∈ prX (Cgrp J h), deltaR c g = 1) → ∃ f, IsCosetFn J h f ∧ f h = 1 := by
  first | exact @GlobalTheory.CosetFn.exists_isCosetFn | exact GlobalTheory.CosetFn.exists_isCosetFn | (intros; apply GlobalTheory.CosetFn.exists_isCosetFn <;> assumption)
