import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCOPrXCgrp
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCO_prX_Cgrp_and_det_valuation_deltaR_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ h : GL (n ⊕ Fin c) k, IsCO (prX (Cgrp J h)) ∧ ∀ g ∈ prX (Cgrp J h), valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 ∧ deltaR c g = 1 := by
  first | exact @GlobalTheory.PrCompactOpen.isCO_prX_Cgrp | exact GlobalTheory.PrCompactOpen.isCO_prX_Cgrp | (intros; apply GlobalTheory.PrCompactOpen.isCO_prX_Cgrp <;> assumption)
