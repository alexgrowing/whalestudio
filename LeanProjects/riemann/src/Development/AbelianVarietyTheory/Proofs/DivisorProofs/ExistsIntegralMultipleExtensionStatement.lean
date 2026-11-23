import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralMultipleExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_multiple_extension : ∀ (F : Type) [Field F] [NumberField F] (X G : Scheme.{0}) (p : X ⟶ Sp (𝓞 F)) (q : G ⟶ Sp F) (j : G ⟶ X), IsPullback j q p (spMap (algebraMap (𝓞 F) F)) → ∀ (W : G.Opens) (x : G), x ∈ W → ∀ (ι : Type) [Fintype ι] (g : ι → Γ(G, W)), ∃ (W' : X.Opens) (h : j ⁻¹ᵁ W' ≤ W), x ∈ j ⁻¹ᵁ W' ∧ ∃ (n : ℕ) (g' : ι → Γ(X, W')), n ≠ 0 ∧ ∀ a, (n : Γ(G, j ⁻¹ᵁ W')) * resG G h (g a) = j.app W' (g' a) := by
  first | exact @GlobalTheory.GenericFibreInt.exists_nat_mul_eq_app | exact GlobalTheory.GenericFibreInt.exists_nat_mul_eq_app | (intros; apply GlobalTheory.GenericFibreInt.exists_nat_mul_eq_app <;> assumption)
