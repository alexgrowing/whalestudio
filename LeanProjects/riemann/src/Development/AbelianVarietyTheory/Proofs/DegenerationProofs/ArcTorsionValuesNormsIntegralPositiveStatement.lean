import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcTorsionValuesNormsIntegralPositive
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcTorsionValues_norms_integral_positive : AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing O') C], CExt O' ⊥ C → ∀ A : Lift a C, A.ν.IntN → (∀ χ, ‖(A.N.ψ χ : C)‖ = 1) ∧ (∀ m, Odd m → ∀ (p : A.N.QT (m ^ 2)) χ, ‖A.N.txT m p χ‖ ≤ 1) ∧ ∀ u : Cˣ, ‖(u : C)‖ < 1 → ∃ q : QuadraticMap ℤ A.N.X ℝ, (A.N.twist A.be u).Int q ∧ ∀ y, q y = -Real.log ‖(u : C)‖ * (A.be.be y y / 2) := by
  first | exact @GlobalTheory.Ex.UnitNorm.norms_of_arc_input | exact GlobalTheory.Ex.UnitNorm.norms_of_arc_input | (intros; apply GlobalTheory.Ex.UnitNorm.norms_of_arc_input <;> assumption)
