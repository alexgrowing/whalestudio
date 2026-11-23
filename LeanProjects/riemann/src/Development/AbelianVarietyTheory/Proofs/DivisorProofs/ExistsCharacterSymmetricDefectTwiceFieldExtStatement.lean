import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharacterSymmetricDefectTwiceFieldExt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_symmetricDefect_twice_fieldExt : ∀ (k k' : Type) [CommRing k] [CommRing k'], IsField k → IsField k' → ∀ (ρ : k →+* k') (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (G'₀ : Over (Sp k')) [GrpObj G'₀] [IsCommMonObj G'₀] (β₀ : G'₀.left ⟶ G₀.left) (hβ₀ : IsGrpPullback G'₀ G₀ (spMap ρ) β₀) (P₀ : GlobalTheory.UU.CP G₀) (P'₀ : GlobalTheory.UU.CP G'₀) (w₀ : LB.Iso P'₀.L.L (P₀.L.L.pull β₀)), GlobalTheory.UU.IsCPMap P'₀ P₀ (spMap ρ) β₀ hβ₀.1.w w₀ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G₀) (i₁ : splitTorus (Sp k') X ⟶ G'₀), IsMonHom i → IsMonHom i₁ → GlobalTheory.UU.TorusCompat (spMap ρ) β₀ i₁ i → ∀ (σ : GlobalTheory.UU.CubTriv P₀.c i) (σ₁ : GlobalTheory.UU.CubTriv P'₀.c i₁), GlobalTheory.UU.CubTriv.Even (P := P'₀) σ₁ → ∃ χ : X, GlobalTheory.UU.CubTriv.Even (P := P₀) (σ.twist χ) := by
  first | exact @GlobalTheory.TwistCompare.exists_twist_even | exact GlobalTheory.TwistCompare.exists_twist_even | (intros; apply GlobalTheory.TwistCompare.exists_twist_even <;> assumption)
