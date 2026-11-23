import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationScaledMultiple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_scaled_multiple : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) (ψ φ : InvFun (𝓞 E)) (x y m n : ℕ) (BD : EffCartierData Z.X), 0 < n → IsPol (comb x ψ y φ) m Z BD → ∃ BD' : EffCartierData Z.X, IsPol (comb (n * x) ψ (n * y) φ) (n * m) Z BD' := by
  first | exact @GlobalTheory.TorRef.Scale.scale_pol | exact GlobalTheory.TorRef.Scale.scale_pol | (intros; apply GlobalTheory.TorRef.Scale.scale_pol <;> assumption)
