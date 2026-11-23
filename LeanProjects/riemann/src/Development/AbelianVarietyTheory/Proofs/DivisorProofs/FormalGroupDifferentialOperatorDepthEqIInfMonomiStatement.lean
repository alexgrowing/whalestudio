import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDifferentialOperatorDepthEqIInfMonomi
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupDifferentialOperatorDepth_eq_iInf_monomial : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (P : MvPolynomial (Σ b, ι b) C), depth G u P = ⨅ β ∈ {β : (Σ b, Fin (d b)) →₀ ℕ | β.degree ≤ P.totalDegree}, toE (v (derivAt0 P (subst (expAlong G u) (monomial β (1 : C))))) := by
  first | exact @GlobalTheory.DepthDegree.depth_eq_iInf_monomial_degree_le | exact GlobalTheory.DepthDegree.depth_eq_iInf_monomial_degree_le | (intros; apply GlobalTheory.DepthDegree.depth_eq_iInf_monomial_degree_le <;> assumption)
