import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelSmallSectionsMul
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
theorem _root_.GlobalTheory.T.model_small_sections_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (u v : GlobalTheory.AllWt.Weight Dw) (R R' : ℝ), 0 ≤ R → 0 ≤ R' → ∀ s ∈ modelSmall (o.toTowerOrigin.Or B b) u R, ∀ s' ∈ modelSmall (o.toTowerOrigin.Or B b) v R', s * s' ∈ modelSmall (o.toTowerOrigin.Or B b) (u + v) (R * R') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.modelSmall_mul_mem | exact GlobalTheory.CompanionTheory.Ar.Plug.modelSmall_mul_mem | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.modelSmall_mul_mem <;> assumption)
