import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelPullback_iff_eighthPower_pullback : Out.Laws → Out.Laws2 → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (c : SiegPre h k (b.ζ : o) s) (c' : SiegPre h k (b.ζ : o) s') (t : TObj g k J b s) (t' : TObj g k J b s') (f : S' ⟶ S), c.Principal → c'.Principal → IsSharp W a bas t c → IsSharp W a bas t' c' → (SiegPB c' c f → TMap t' t f) ∧ ((∀ u v, ∃ j, a j = Matrix.single u v 1) → TMap t' t f → SiegPB c' c f) := by
  first | exact @GlobalTheory.PowerPullback.main | exact GlobalTheory.PowerPullback.main | (intros; apply GlobalTheory.PowerPullback.main <;> assumption)
