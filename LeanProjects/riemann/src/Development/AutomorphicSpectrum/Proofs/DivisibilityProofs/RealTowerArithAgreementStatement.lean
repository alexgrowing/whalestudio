import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerArithAgreement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_tower_arith_agreement : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))) (n : ℕ) (R : RealTie M S n) (lam : Wt Ψ N) (s : ℝ), 0 < n ∧ (∀ t, 0 < t → t ≤ S.t₀ → (n : ℝ) * M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) = eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) (R.Re.FT II t)) ∧ ((∀ w, Tendsto (fun t => R.Re.num II t w) (𝓝[>] 0) (𝓝 (R.Re.limNum II w))) → 0 < S.t₀ → M.Converges II ∧ (n : ℝ) * M.PP II (linA lam s ^ (dimFl Ψ N + 1)) = eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) (R.Re.PB II)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.RootNum.arith_degrees | exact GlobalTheory.CompanionTheory.Ar.Top.RootNum.arith_degrees | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.RootNum.arith_degrees <;> assumption)
