import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearIndependentVecMulOfSpanRat
import Mathlib
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_vecMul_of_span_rat' : ∀ (E : Type) [Field E] [NumberField E] (R : Type) [CommRing R] [Algebra ℝ R] [FiniteDimensional ℝ R] (τ : E →+* R), Submodule.span ℝ (Set.range τ) = ⊤ → Module.finrank ℝ R = Module.finrank ℚ E → ∀ (n : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin n → E), Fintype.card ι = Module.finrank ℚ E * n → Submodule.span ℚ (Set.range u) = ⊤ → ∀ g : GL (Fin n) R, LinearIndependent ℝ fun k => (fun i => τ (u k i)) ᵥ* g.1 := by
  first | exact @GlobalTheory.linearIndependent_vecMul_of_span_rat | exact GlobalTheory.linearIndependent_vecMul_of_span_rat | (intros; apply GlobalTheory.linearIndependent_vecMul_of_span_rat <;> assumption)
