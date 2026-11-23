import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicHaarVolumeConjIntersectionEqMul
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicHaarVolume_conjIntersection_eq_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k), IsOpen (prX (Cgrp J h) : Set (GL n k)) → ∀ m : Measure (GL n k), volR ν m (Cgrp J h) = volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1)) * m (prX (Cgrp J h)) := by
  first | exact @GlobalTheory.CosetVolProd.volR_Cgrp | exact GlobalTheory.CosetVolProd.volR_Cgrp | (intros; apply GlobalTheory.CosetVolProd.volR_Cgrp <;> assumption)
