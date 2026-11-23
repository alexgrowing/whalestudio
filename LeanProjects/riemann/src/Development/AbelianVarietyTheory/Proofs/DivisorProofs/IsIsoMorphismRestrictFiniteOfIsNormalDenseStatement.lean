import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoMorphismRestrictFiniteOfIsNormalDense
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoNearNormalPointOfFiniteBirational
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_morphismRestrict_finite_of_isNormal_dense : ∀ {S T : Scheme.{0}} [IsLocallyNoetherian T] (ν : S ⟶ T) [IsFinite ν] (U V : T.Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (V : Scheme.{0}) → Dense (U : Set T) → Dense (ν ⁻¹' (U : Set T)) → IsIso (ν ∣_ U) → IsIso (ν ∣_ V) := by
  first | exact @GlobalTheory.FiniteBirationalNear.isIso_morphismRestrict_of_isNormal | exact GlobalTheory.FiniteBirationalNear.isIso_morphismRestrict_of_isNormal | (intros; apply GlobalTheory.FiniteBirationalNear.isIso_morphismRestrict_of_isNormal <;> assumption)
