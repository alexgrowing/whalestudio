import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreePolynomialEval
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_degree_polynomial_eval : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (lam : Wt Ψ N), 2 ≤ N → eval (fun x => lam x.1 x.2) (PB.degFlPoly Ψ N) = flagDeg lam := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_degree_polynomial_eval | exact GlobalTheory.CompanionTheory.Relay.flag_degree_polynomial_eval | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_degree_polynomial_eval <;> assumption)
