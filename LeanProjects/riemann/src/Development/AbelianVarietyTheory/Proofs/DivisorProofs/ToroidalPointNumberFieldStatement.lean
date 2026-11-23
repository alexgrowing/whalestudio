import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalPointNumberField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_point_number_field : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (K : Type) [Field K] [NumberField K] (jF : c.F →+* K) (yK : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ GlobalTheory.Toroidal.gen Z), yK ≫ GlobalTheory.Toroidal.genStr Z = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap jF → ∃ yO : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (𝓞 K) ⟶ Z.X, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap (𝓞 K) K) ≫ yO = yK ≫ GlobalTheory.Toroidal.genι Z := by
  first | exact @GlobalTheory.ModelPointExt.exists_integral_extension | exact GlobalTheory.ModelPointExt.exists_integral_extension | (intros; apply GlobalTheory.ModelPointExt.exists_integral_extension <;> assumption)
