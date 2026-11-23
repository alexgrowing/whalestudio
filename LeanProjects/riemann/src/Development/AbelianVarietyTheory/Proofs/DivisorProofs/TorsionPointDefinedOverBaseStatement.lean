import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointDefinedOverBase
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_point_defined_over_base : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (N : ℕ), 1 ≤ N → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp ℂ) (y : Over.mk t ⟶ X.A), y ^ N = 1 → ∃ z : 𝟙_ (Over (Sp ℂ)) ⟶ X.A, y = toUnit (Over.mk t) ≫ z := by
  first | exact @GlobalTheory.RealMult.torsion_descends_to_complex | exact GlobalTheory.RealMult.torsion_descends_to_complex | (intros; apply GlobalTheory.RealMult.torsion_descends_to_complex <;> assumption)
