import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyIntegral_of_affCover : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ), AffCover M M' φ f r → GeometricallyIntegral M.s → GeometricallyIntegral M'.s := by
  first | exact @GlobalTheory.FlagBundle.AffCover.geometricallyIntegral | exact GlobalTheory.FlagBundle.AffCover.geometricallyIntegral | (intros; apply GlobalTheory.FlagBundle.AffCover.geometricallyIntegral <;> assumption)
