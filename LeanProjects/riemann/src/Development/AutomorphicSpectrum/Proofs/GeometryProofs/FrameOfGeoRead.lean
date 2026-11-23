import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Plug.RdGeo

theorem frame_of_geoRead : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (_ : GeoRead Rd), letI := Small.cstAlg (o.toTowerOrigin.Or B b); ∃ (φ : Om Z →ₐ[c.F] (T.M B b).Ω) (P : FrPt Xo c (T.M B b).Ω) (t : Ix Dw → ((T.M B b).Ω)ˣ), (∀ x, φ x = Rd.φ x) ∧ FrMap φ (genFr h Z) P ∧ FrBor t P Fr.y₀ ∧ ∀ i, i ≠ none → t i = Rd.t i := by
  intro hG E _ _ _ H Dw l Xo c r U h e hC Y _ T o B b Fr Z Rd hg
  letI := Small.cstAlg (o.toTowerOrigin.Or B b)
  obtain ⟨y', hm, hb⟩ := hg
  exact ⟨{ Rd.φ with commutes' := Rd.φ_cst }, y', Rd.t, fun _ => rfl, hm, hb, fun _ _ => rfl⟩

end GlobalTheory.CompanionTheory.Ar.Plug.RdGeo
