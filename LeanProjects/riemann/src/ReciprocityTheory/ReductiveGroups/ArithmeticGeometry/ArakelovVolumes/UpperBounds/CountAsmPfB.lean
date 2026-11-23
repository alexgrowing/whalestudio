import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountAsm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetsPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLE

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Asymptotics

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ss_mul_pow {r : ℕ} (X : Data E r) {la L : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ}
    (hP : P ∈ X.SS la) (hQ : X.IsBddSec L Q) (k : ℕ) : P * Q ^ k ∈ X.SS (la + k • L) := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    have h := (siegelSpaceAlgebra_holds r X (la + k • L) L 0).2.1 (P * Q ^ k) ih Q hQ
    rw [pow_succ, ← mul_assoc, succ_nsmul, ← add_assoc]
    exact h

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
