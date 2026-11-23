import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendFiniteOverNormalDense
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_finite_over_normal_dense : ∀ (T P Q : Scheme.{0}) (p : P ⟶ Q) (a : T ⟶ Q) (V : T.Opens) (a₀ : V.toScheme ⟶ P), IsFinite p →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → IsLocallyNoetherian T → Dense (V : Set T) → a₀ ≫ p = V.ι ≫ a →
    ∃ a' : T ⟶ P, a' ≫ p = a ∧ V.ι ≫ a' = a₀ := by
  first | exact @GlobalTheory.exists_lift_of_isFinite_of_dense_opens | exact GlobalTheory.exists_lift_of_isFinite_of_dense_opens | (intros; apply GlobalTheory.exists_lift_of_isFinite_of_dense_opens <;> assumption)
