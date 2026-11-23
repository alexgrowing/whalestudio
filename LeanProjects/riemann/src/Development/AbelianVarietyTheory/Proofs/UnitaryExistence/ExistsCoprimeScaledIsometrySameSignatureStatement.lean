import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoprimeScaledIsometrySameSignature
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_scaled_isometry_same_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H), D'.p = D.p → D'.q = D.q → ∀ b : ℕ, 0 < b → ∃ (k : ℕ) (f : D.La →ₗ[𝓞 E] D'.La), k.Coprime b ∧ ∀ x y, D'.EF (f x) (f y) = (k : ℤ) ^ 2 * D.EF x y := by
  first | exact @GlobalTheory.LocalIsomAt.exists_coprime_scaled_isometry | exact GlobalTheory.LocalIsomAt.exists_coprime_scaled_isometry | (intros; apply GlobalTheory.LocalIsomAt.exists_coprime_scaled_isometry <;> assumption)
