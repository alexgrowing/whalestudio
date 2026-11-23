import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraFiniteProjectiveRank
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_finite_projective_rank : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)),
    Module.Finite R X.Lie ∧ Module.Projective R X.Lie ∧ ∀ p, Module.rankAtStalk (R := R) X.Lie p = Module.finrank ℚ F := by
  first | exact @GlobalTheory.LieProj.lie_finite_projective_rank | exact GlobalTheory.LieProj.lie_finite_projective_rank | (intros; apply GlobalTheory.LieProj.lie_finite_projective_rank <;> assumption)
