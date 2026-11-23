import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationExtensionField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_extension_field : ∀ (F F' : IntermediateField ℚ ℂ) (hle : F ≤ F'), FiniteDimensional ℚ F' → ∀ (W : ValuationSubring ℂ) (K : Type) [Field K] [IsAlgClosed K] (O : ValuationSubring K) (g : F →+* K), (∀ x : F, (x : ℂ) ∈ W ↔ g x ∈ O) → ∃ g' : F' →+* K, (∀ x : F, g' (IntermediateField.inclusion hle x) = g x) ∧ ∀ x : F', (x : ℂ) ∈ W → g' x ∈ O := by
  first | exact @GlobalTheory.PlaceExt.exists_extend_compatible | exact GlobalTheory.PlaceExt.exists_extend_compatible | (intros; apply GlobalTheory.PlaceExt.exists_extend_compatible <;> assumption)
