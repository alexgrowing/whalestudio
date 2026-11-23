import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGeneratorOffClosedSubscheme
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Matched
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_generator_off_closed_subscheme : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (L' : LB X'), L'.IsLB → ∀ x : X, (∀ z : Z, i z ≠ x) → ∃ (W : X.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ p ⁻¹ᵁ W)ˣ), x ∈ W ∧ i ⁻¹ᵁ W = ⊥ ∧ GlobalTheory.PinchLift.GenOn L' (p ⁻¹ᵁ W) s' := by
  first | exact @GlobalTheory.PinchLift.exists_gen_away_of_closed | exact GlobalTheory.PinchLift.exists_gen_away_of_closed | (intros; apply GlobalTheory.PinchLift.exists_gen_away_of_closed <;> assumption)
