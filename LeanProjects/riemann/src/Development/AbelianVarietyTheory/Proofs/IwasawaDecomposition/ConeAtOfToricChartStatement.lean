import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeAtOfToricChart
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coneAt_of_toric_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (φ : InvFun (𝓞 E)) (Y : Model Xo c (RingHom.id c.F)) (BD : GlobalTheory.EffCartierData Y.X) (d : ℕ) (x : gen Y), GlobalTheory.MumfordChart.HasChartOf φ Y BD d x → GlobalTheory.GenFan.ConeAt (ConeO H φ) Y (genι Y x) := by
  first | exact @GlobalTheory.ChartCone.coneAt_of_hasChartOf | exact GlobalTheory.ChartCone.coneAt_of_hasChartOf | (intros; apply GlobalTheory.ChartCone.coneAt_of_hasChartOf <;> assumption)
