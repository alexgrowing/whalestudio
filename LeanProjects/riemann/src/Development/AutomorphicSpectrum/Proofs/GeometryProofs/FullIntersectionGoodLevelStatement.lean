import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionGoodLevel
import Mathlib
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
theorem _root_.GlobalTheory.T.full_intersection_good_level : Top.Given → Top.GoodTowerExistsX → Top.VolumeTheoremX → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [DecidableEq (CMType H)] (II : IntersectionSystem), IsFullIntersectionSystem II → FnAlgClosed Xo c → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → 1 ≤ Dw.q → 3 * Dw.q + 1 ≤ Dw.p + Dw.q → (2 * discr E * l.M').natAbs.primeFactors.card ≤ 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 → ∃ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp), o.Extra ∧ CompOf o.toTowerOrigin κ ∧ T.bad = (2 * discr E * l.M').natAbs.primeFactors ∧ T.Proportional ∧ T.T1 II ∧ T.VolEq ∧ T.MeanSlope II C (hostRd E) (hostLval H) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.vs_tower | exact GlobalTheory.CompanionTheory.Ar.Plug.vs_tower | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.vs_tower <;> assumption)
