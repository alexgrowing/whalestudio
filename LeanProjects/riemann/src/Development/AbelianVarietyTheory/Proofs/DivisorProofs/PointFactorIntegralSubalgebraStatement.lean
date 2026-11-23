import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointFactorIntegralSubalgebra
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_through_integral_subalgebra : ∀ (K B E : Type) [Field K] [CommRing B] [CommRing E] [Algebra K B] [Algebra K E] (i : E →ₐ[K] B), Function.Injective i → (∀ b : B, _root_.IsIntegral K b → b ∈ i.range) → ∀ (T : Scheme.{0}) (p : T ⟶ Sp K) [IsFinite p] (t : Sp B ⟶ T), t ≫ p = spMap (algebraMap K B) → ∃ u : Sp E ⟶ T, u ≫ p = spMap (algebraMap K E) ∧ t = spMap i.toRingHom ≫ u := by
  first | exact @GlobalTheory.point_factor_integral_subalgebra | exact GlobalTheory.point_factor_integral_subalgebra | (intros; apply GlobalTheory.point_factor_integral_subalgebra <;> assumption)
