import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSubextensionPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_subextension_point : ∀ (X S : Scheme.{0}) (s : X ⟶ S), LocallyOfFiniteType s → ∀ (K₀ K : Type) [Field K₀] [Field K] [Algebra K₀ K], Algebra.IsAlgebraic K₀ K → ∀ (y : Sp K ⟶ X) (z : Sp K₀ ⟶ S), y ≫ s = spMap (algebraMap K₀ K) ≫ z → ∃ (L : IntermediateField K₀ K) (yL : Sp L ⟶ X), FiniteDimensional K₀ L ∧ spMap (algebraMap L K) ≫ yL = y ∧ yL ≫ s = spMap (algebraMap K₀ L) ≫ z := by
  first | exact @GlobalTheory.FinDesc.exists_finite_subext_point | exact GlobalTheory.FinDesc.exists_finite_subext_point | (intros; apply GlobalTheory.FinDesc.exists_finite_subext_point <;> assumption)
