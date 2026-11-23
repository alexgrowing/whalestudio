import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianCmCompLawsBound
import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_cm_comp_laws_bound : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ArithIntersectionSystemStatement → BirationalPullbackPushforwardFormula → Top.GoodTowerExistsX → Top.VolumeTheoremX → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → FnAlgClosed Xo c → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → 1 ≤ Dw.q → 3 * Dw.q + 1 ≤ Dw.p + Dw.q → 2 ≤ Fintype.card (CMType H) → (Nat.primeFactors (2 * (discr E).natAbs) ∪ l.M'.primeFactors).card ≤ 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → GlobalTheory.CovHt.MeanAll U x (Real.log (hostRd E) + |hostLval H|) C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.top_meanAll | exact GlobalTheory.CompanionTheory.Ar.Plug.top_meanAll | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.top_meanAll <;> assumption)
