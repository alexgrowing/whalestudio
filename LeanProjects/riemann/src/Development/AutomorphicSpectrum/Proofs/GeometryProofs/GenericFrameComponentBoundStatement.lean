import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFrameComponentBound
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
theorem _root_.GlobalTheory.T.generic_frame_component_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (h : GenFrEx Xo c), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (II : IntersectionSystem) (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ), IsFullIntersectionSystem II → T.T1 II → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g < B + 1 → ∃ (k₀ : ℕ) (R₀ : ℝ) (f : Fin (o.toTowerOrigin.Or B b).Fl.deg → (T.M B b).Ω), 8 ∣ k₀ ∧ 0 < R₀ ∧ (∀ i, f i ∈ modelSmall (o.toTowerOrigin.Or B b) (k₀ • u) R₀) ∧ (∀ a : Fin (o.toTowerOrigin.Or B b).Fl.deg → Om Z, ∑ i, Rd.φ (a i) * f i = 0 → a = 0) ∧ ∀ (v : GlobalTheory.AllWt.Weight Dw) (s : (T.M B b).Ω), (∀ i, trOf Rd v (s * f i) = 0) → s = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.exists_small_basis | exact GlobalTheory.CompanionTheory.Ar.Plug.exists_small_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.exists_small_basis <;> assumption)
