import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalPointClosedPointImage
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_point_closed_point_image : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (K : Type) [Field K] [NumberField K] (yK : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ GlobalTheory.Toroidal.gen Z), yK (IsLocalRing.closedPoint K) ∉ GlobalTheory.Toroidal.genBd Z → ∃ (P₀ : ReciprocityTheory.ChartRestriction.G.Out.PolAV (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (θ : P₀.A.left ⟶ Z.t.G.left), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback P₀.A Z.t.G (yK ≫ GlobalTheory.Toroidal.genι Z) θ ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso (Z.t.PP.L.pull θ) P₀.L := by
  first | exact @GlobalTheory.InteriorFibre.exists_polAV_of_not_mem_genBd | exact GlobalTheory.InteriorFibre.exists_polAV_of_not_mem_genBd | (intros; apply GlobalTheory.InteriorFibre.exists_polAV_of_not_mem_genBd <;> assumption)
