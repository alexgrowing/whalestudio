import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAuxiliaryMetricPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_auxiliary_metric_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (T : Tw Z) (x : OddPrimesWithRootsOfUnity Z), ∃ x₂ : OddPrimesWithRootsOfUnity Z, ∀ σ y, T.MetAt y (x.eigMet σ) (x₂.eigMet σ) := by
  first | exact @GlobalTheory.ShFam.GalCarry.exists_auxiliary_data_metric | exact GlobalTheory.ShFam.GalCarry.exists_auxiliary_data_metric | (intros; apply GlobalTheory.ShFam.GalCarry.exists_auxiliary_data_metric <;> assumption)
