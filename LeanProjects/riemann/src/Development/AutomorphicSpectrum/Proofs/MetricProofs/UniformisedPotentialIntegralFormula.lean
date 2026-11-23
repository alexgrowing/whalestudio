import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XPerInt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem proportional_on_uniformised : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (U : Set X) (th : Ψ × Fin N → LocPot X) (ph : Ψ × Fin N → X → ℝ), j ≤ N → e = antisymDegree Ψ N → IsOpen U → IsNull A Uᶜ → (∀ p, IsPotential A (th p)) → (∀ p, A.SmoothOn U (ph p)) → IsUniformised A U j (fun p => th p + LocPot.ofFun (ph p)) → (∀ w : Fin e → Ψ × Fin N, MIntegrable A (fun i => th (w i) + LocPot.ofFun (ph (w i))) (fun _ => 1)) → ∃ v : ℝ, 0 < v ∧ toWt (formPoly e fun w => mInt A (fun i => th (w i) + LocPot.ofFun (ph (w i))) (fun _ => 1)) = C v * antisymDelta Ψ N :=
  @PositivityTheory.Xgp.t_per_int

end GlobalTheory.CompanionTheory.Ar.PB
