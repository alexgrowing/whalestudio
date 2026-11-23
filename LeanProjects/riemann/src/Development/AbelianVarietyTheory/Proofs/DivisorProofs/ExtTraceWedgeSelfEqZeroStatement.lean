import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtTraceWedgeSelfEqZero
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ext_trace_wedge_self_eq_zero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (ξ₁ η₁ ξ₂ η₂ : V), wedge (extTrace H z) (extTrace H z) ξ₁ η₁ ξ₂ η₂ = 0 := by
  first | exact @GlobalTheory.extTrace_wedge_self_eq_zero_of_line | exact GlobalTheory.extTrace_wedge_self_eq_zero_of_line | (intros; apply GlobalTheory.extTrace_wedge_self_eq_zero_of_line <;> assumption)
