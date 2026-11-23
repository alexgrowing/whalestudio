import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeEndomorphismExtOfDensePoint
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_endomorphism_ext_of_dense_point : ∀ (W : Scheme.{0}) [IsIntegral W] (G : Over W) [GrpObj G], IsAbelianScheme G → ∀ (Ω : Type) [Field Ω] (pt : Sp Ω ⟶ W), Dense (Set.range pt) → ∀ (f f' : G ⟶ G), pullback.fst G.hom pt ≫ f.left = pullback.fst G.hom pt ≫ f'.left → f = f' := by
  first | exact @GlobalTheory.abelianScheme_end_ext_of_dense | exact GlobalTheory.abelianScheme_end_ext_of_dense | (intros; apply GlobalTheory.abelianScheme_end_ext_of_dense <;> assumption)
