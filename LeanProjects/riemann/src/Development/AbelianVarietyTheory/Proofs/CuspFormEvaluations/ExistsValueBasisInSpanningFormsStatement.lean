import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsValueBasisInSpanningForms
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DescentStatementPf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valueBasis_in_spanning_forms : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (N : ℕ) (w : Fin N → B.Cusp j wL) (R : Rdg X) (t : Idx D j N → ℂ) (T : ℕ) (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y), AnFacts R w t ka wF T Mg xs → ∀ Sh : Set (B.Cusp j wF), Submodule.span B.KO Sh = ⊤ → ∃ θ : Fin δ → B.Cusp j wF, (∀ i, θ i ∈ Sh) ∧ LinearIndependent ℂ (vals xs fun i => R.ev (X.inc wF (θ i))) := by
  first | exact @GlobalTheory.Shares.exists_valueBasis_in_spanning | exact GlobalTheory.Shares.exists_valueBasis_in_spanning | (intros; apply GlobalTheory.Shares.exists_valueBasis_in_spanning <;> assumption)
