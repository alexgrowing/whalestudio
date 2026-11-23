import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationComapOpenImmersion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Reg GlobalTheory.FlagMod

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_comap_open_immersion : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (v : Y'.X ⟶ Y.X), ∀ (DY : EffCartierData Y.X) (DY' : EffCartierData Y'.X) (m : ℕ), IsOpenImmersion v → Nonempty (SABMap Y'.t Y.t v) → DY.idealSheaf.comap v = DY'.idealSheaf → ((polOf Y m DY).pull v).IsLB → (polOf Y' m DY').IsLB → LBIso (polOf Y' m DY') ((polOf Y m DY).pull v) := by
  first | exact @GlobalTheory.PolPull.lbIso_polOf_pull | exact GlobalTheory.PolPull.lbIso_polOf_pull | (intros; apply GlobalTheory.PolPull.lbIso_polOf_pull <;> assumption)
