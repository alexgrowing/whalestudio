import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bridge

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive LinkPer KroneckerLimit DedekindFactor)
open Formalism.MainNotions.TaylorLogMetric (lamConj lamOf embT meanLogOm DataIn tor0 IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice per22 logOmVal)

theorem br_sum_log_norm_sq (M : IntermediateField ℚ ℂ) [NumberField M] (s : M) (hs : s ≠ 0) :
    ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (‖ρ s‖ ^ 2) = 2 * Real.log |((Algebra.norm ℚ s : ℚ) : ℝ)| := by
  have hρ : ∀ ρ : M →ₐ[ℚ] ℂ, ρ s ≠ 0 := fun ρ => (map_ne_zero ρ).2 hs
  rw [← Real.log_prod (fun ρ _ => by have := hρ ρ; positivity)]
  have hN := Algebra.norm_eq_prod_embeddings ℚ ℂ s
  have h1 : ∏ ρ : M →ₐ[ℚ] ℂ, ‖ρ s‖ ^ 2 = |((Algebra.norm ℚ s : ℚ) : ℝ)| ^ 2 := by
    rw [Finset.prod_pow, ← norm_prod]
    convert congrArg (fun z : ℂ => ‖z‖ ^ 2) hN.symm using 2
    simp
  rw [h1, Real.log_pow]
  push_cast; ring

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
