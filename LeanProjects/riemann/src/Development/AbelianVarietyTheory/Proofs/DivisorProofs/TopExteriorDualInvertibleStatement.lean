import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopExteriorDualInvertible
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_exterior_dual_invertible : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (n : ℕ), (∀ p, Module.rankAtStalk (R := R) M p = n) → Module.Invertible R (M [⋀^Fin n]→ₗ[R] R) := by
  first | exact @GlobalTheory.InvertibleTopExteriorPower.invertible_alternatingMap_top | exact GlobalTheory.InvertibleTopExteriorPower.invertible_alternatingMap_top | (intros; apply GlobalTheory.InvertibleTopExteriorPower.invertible_alternatingMap_top <;> assumption)
