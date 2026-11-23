import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfB
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD

variable {f p q N' : ℕ}

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
  | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
  | exact WithTop.coe_le_coe.mpr le_top
  | simp

theorem sqNorm_nonneg' {m : ℕ} (g : Fin m → ℂ) : 0 ≤ sqNorm g :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhF

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE

variable {f p q N' : ℕ}

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhF
