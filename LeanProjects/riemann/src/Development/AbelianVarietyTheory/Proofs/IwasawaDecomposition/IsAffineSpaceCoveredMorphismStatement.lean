import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAffineSpaceCoveredMorphism
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineSpaceCoveredMorphism : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J] [DecidableEq J] (EE : M.Lat J) (s : J → Ω'), ProjBundle M EE M' φ f s → AffCover M M' φ f (Fintype.card J - 1) := by
  first | exact @GlobalTheory.FlagBundle.ProjBundle.affCover | exact GlobalTheory.FlagBundle.ProjBundle.affCover | (intros; apply GlobalTheory.FlagBundle.ProjBundle.affCover <;> assumption)
