import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionHeightBound
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
theorem _root_.GlobalTheory.T.full_intersection_height_bound : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (II : IntersectionSystem) (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ), IsFullIntersectionSystem II → T.T1 II → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g < B + 1 → ∀ ε : ℝ, 0 < ε → ∃ᶠ τ : ℕ in atTop, ∃ (n : ℕ) (f : Fin n → (T.M B b).Ω), LinearIndependent ℤ f ∧ (∀ i, ∃ R, f i ∈ modelSmall (o.toTowerOrigin.Or B b) (τ • u) R) ∧ ((T.M B b).δ * (T.vol b * Top.flagDeg (reW u)) - ε) * (τ : ℝ) ^ (Top.dimFl (CMType H) (Dw.p + Dw.q)) ≤ ((Top.dimFl (CMType H) (Dw.p + Dw.q)).factorial : ℝ) * n := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.many_sections | exact GlobalTheory.CompanionTheory.Ar.Plug.many_sections | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.many_sections <;> assumption)
