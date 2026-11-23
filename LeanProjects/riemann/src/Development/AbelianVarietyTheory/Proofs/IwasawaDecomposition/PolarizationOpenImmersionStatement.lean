import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationOpenImmersion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_open_immersion : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (v : Y'.X ⟶ Y.X) (DY : EffCartierData Y.X) (DY' : EffCartierData Y'.X) (m : ℕ), IsOpenImmersion v → Nonempty (SABMap Y'.t Y.t v) → DY.idealSheaf.comap v = DY'.idealSheaf → (GlobalTheory.IsAmpleLB (polOf Y' m DY') ↔ GlobalTheory.IsAmpleLB ((polOf Y m DY).pull v)) := by
  first | exact @GlobalTheory.PolOpen.isAmpleLB_polOf_iff_pull | exact GlobalTheory.PolOpen.isAmpleLB_polOf_iff_pull | (intros; apply GlobalTheory.PolOpen.isAmpleLB_polOf_iff_pull <;> assumption)
