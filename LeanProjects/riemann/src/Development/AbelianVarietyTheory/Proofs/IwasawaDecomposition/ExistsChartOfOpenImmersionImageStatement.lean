import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartOfOpenImmersionImage
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Reg GlobalTheory.FlagMod

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_of_open_immersion_image : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (v : Y'.X ⟶ Y.X), IsOpenImmersion v → Nonempty (SABMap Y'.t Y.t v) → ∀ (M' : MChart Y') (y : Y'.X), y ∈ M'.U → ∃ M : MChart Y, v y ∈ M.U := by
  first | exact @GlobalTheory.ChartTransport.exists_chart_image | exact GlobalTheory.ChartTransport.exists_chart_image | (intros; apply GlobalTheory.ChartTransport.exists_chart_image <;> assumption)
