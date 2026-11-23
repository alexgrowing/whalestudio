import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusFactorBaseChangeField
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_factor_baseChange_field : ∀ (k k' : Type) [CommRing k] [CommRing k'], IsField k' → ∀ (ρ : k →+* k') (G₀ : Over (Sp k)) [GrpObj G₀] (G'₀ : Over (Sp k')) [GrpObj G'₀] (β₀ : G'₀.left ⟶ G₀.left), IsGrpPullback G'₀ G₀ (spMap ρ) β₀ → ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] (Q₀ : GlobalTheory.UU.TQ G₀ X) (Q'₀ : GlobalTheory.UU.TQ G'₀ X'), ∃ (i₁ : splitTorus (Sp k') X ⟶ G'₀) (e : splitTorus (Sp k') X ⟶ splitTorus (Sp k') X'), IsMonHom e ∧ e ≫ Q'₀.i = i₁ ∧ GlobalTheory.UU.TorusCompat (spMap ρ) β₀ i₁ Q₀.i := by
  first | exact @GlobalTheory.Mum.exists_torus_factor | exact GlobalTheory.Mum.exists_torus_factor | (intros; apply GlobalTheory.Mum.exists_torus_factor <;> assumption)
