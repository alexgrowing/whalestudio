import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFractionalIdealTraceFormRankOne
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fractionalIdeal_traceForm_rank_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), D.p + D.q = 1 → IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (e : D.La →ₗ[𝓞 E] E) (β : E), 𝔞 ≠ 0 ∧ Function.Injective e ∧ LinearMap.range e = (𝔞 : Submodule (𝓞 E) E) ∧ IsCMField.complexConj E β = β ∧ (∀ τ : E →+* ℂ, 0 < (τ β).re) ∧
  (∀ (Ω : Type) [Field Ω] [CharZero Ω], Nat.card (E →+* Ω) = Module.finrank ℚ E → ∀ (τ₀ : E →+* Ω) x y, τ₀ (((h x y : OK H) : 𝓞 E) : E) = ∑ᶠ τ : {τ : E →+* Ω // τ (H.rt : E) = τ₀ (H.rt : E)}, τ.1 (β * e x * IsCMField.complexConj E (e y))) ∧
  2 * Real.log (FractionalIdeal.absNorm 𝔞 : ℚ) + Real.log |(Algebra.norm ℚ β : ℚ)| = Module.finrank ℚ E * (Real.log H.d / 2 - Real.log (NumberField.rootDiscr E)) := by
  first | exact @GlobalTheory.CM.exists_ideal_traceForm_of_rank_one | exact GlobalTheory.CM.exists_ideal_traceForm_of_rank_one | (intros; apply GlobalTheory.CM.exists_ideal_traceForm_of_rank_one <;> assumption)
