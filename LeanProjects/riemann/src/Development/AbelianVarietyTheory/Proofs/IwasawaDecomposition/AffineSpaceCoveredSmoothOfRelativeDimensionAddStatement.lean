import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineSpaceCoveredSmoothOfRelativeDimensionAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineSpaceCovered_smoothOfRelativeDimension_add : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r d : ℕ), AffCover M M' φ f r → SmoothOfRelativeDimension d M.s → SmoothOfRelativeDimension (d + r) M'.s := by
  first | exact @GlobalTheory.FlagBundle.affCover_smooth | exact GlobalTheory.FlagBundle.affCover_smooth | (intros; apply GlobalTheory.FlagBundle.affCover_smooth <;> assumption)
