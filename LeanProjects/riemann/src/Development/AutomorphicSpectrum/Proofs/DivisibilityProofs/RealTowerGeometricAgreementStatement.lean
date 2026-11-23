import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerGeometricAgreement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_tower_geometric_agreement : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))) (n : ℕ) (R : RealTie M S n) (lam : Wt Ψ N) (s : ℝ), (n : ℝ) * M.geoFun (linA lam s ^ dimFl Ψ N) = eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) S.degPoly := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.geoFun_linA_pow_of_realTie | exact GlobalTheory.CompanionTheory.Ar.Top.geoFun_linA_pow_of_realTie | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.geoFun_linA_pow_of_realTie <;> assumption)
