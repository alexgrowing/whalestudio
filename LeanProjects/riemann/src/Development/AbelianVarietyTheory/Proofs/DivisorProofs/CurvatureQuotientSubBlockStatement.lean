import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureQuotientSubBlock
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvature_quotient_sub_block : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), blockQS (curv H z ξ η) = -dbarHol (extFormAdj H) z ξ η := by
  first | exact @GlobalTheory.blockQS_curv_eq_neg_dbarHol_extFormAdj | exact GlobalTheory.blockQS_curv_eq_neg_dbarHol_extFormAdj | (intros; apply GlobalTheory.blockQS_curv_eq_neg_dbarHol_extFormAdj <;> assumption)
