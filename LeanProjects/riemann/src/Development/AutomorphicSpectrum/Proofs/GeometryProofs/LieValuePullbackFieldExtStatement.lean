import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieValuePullbackFieldExt
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtComplexEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_value_pullback_field_ext : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (K K' : Type) [Field K] [Field K'] (w : Sp K ⟶ X) (f : K →+* K') (a : Li) (v : epsAt w ⟶ G), M.ValAt w a v → M.ValAt (spMap f ≫ w) a (GlobalTheory.CompanionTheory.Ar.LieSigma.pullEps f w ≫ v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieSigma.ValBC.valAt_field_map | exact GlobalTheory.CompanionTheory.Ar.LieSigma.ValBC.valAt_field_map | (intros; apply GlobalTheory.CompanionTheory.Ar.LieSigma.ValBC.valAt_field_map <;> assumption)
