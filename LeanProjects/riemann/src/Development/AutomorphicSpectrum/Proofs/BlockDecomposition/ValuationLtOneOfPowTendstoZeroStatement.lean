import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfPowTendstoZero
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_lt_one_of_pow_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ t : kˣ, Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) → ValuativeRel.valuation k (t : k) < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Val.valuation_lt_one_of_tendsto_pow_zero | exact GlobalTheory.CompanionTheory.Val.valuation_lt_one_of_tendsto_pow_zero | (intros; apply GlobalTheory.CompanionTheory.Val.valuation_lt_one_of_tendsto_pow_zero <;> assumption)
