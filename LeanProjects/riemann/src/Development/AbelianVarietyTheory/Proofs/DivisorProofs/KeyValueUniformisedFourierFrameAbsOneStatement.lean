import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUniformisedFourierFrameAbsOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.key_value_uniformised_fourier_frame_abs_one : ∀ κ : Rule, Rule4 κ → KapF κ := by
  first | exact @GlobalTheory.MBLow.KapFPf.kapF_of_rule4 | exact GlobalTheory.MBLow.KapFPf.kapF_of_rule4 | (intros; apply GlobalTheory.MBLow.KapFPf.kapF_of_rule4 <;> assumption) | exact @GlobalTheory.MBLow.KapFPf.deform_of_series | exact GlobalTheory.MBLow.KapFPf.deform_of_series | (intros; apply GlobalTheory.MBLow.KapFPf.deform_of_series <;> assumption)
