import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackRadiusData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_radius_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (T : Tw Z) (x : OddPrimesWithRootsOfUnity Z), ∃ x₁ : OddPrimesWithRootsOfUnity Z, ∀ σ y, x₁.r σ y = x.r σ (T.pt y) := by
  first | exact @GlobalTheory.ShFam.AutPull.exists_auxiliary_data_pullback | exact GlobalTheory.ShFam.AutPull.exists_auxiliary_data_pullback | (intros; apply GlobalTheory.ShFam.AutPull.exists_auxiliary_data_pullback <;> assumption)
