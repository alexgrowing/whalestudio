import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfPositiveCoeffOrthogonalEmbeddings
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_positive_coeff_orthogonal_embeddings : ∀ (p q : ℕ) (T : GrpData p q), (∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y) → ∀ (π₁ π₂ : URep T) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (j₁ : E →ₗ[ℂ] π₁.H) (j₂ : E →ₗ[ℂ] π₂.H), Function.Injective j₂ → (∀ k ∈ T.Kset, ∀ w : E, ∃ w' : E, π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') → (∀ Y ∈ pR p q, ∀ w, (inner ℂ (j₁ w) (π₁.π (T.expt Y) (j₁ w))).im = 0 ∧ 0 ≤ (inner ℂ (j₁ w) (π₁.π (T.expt Y) (j₁ w))).re) → (∀ Y ∈ pR p q, ∀ w, (inner ℂ (j₂ w) (π₂.π (T.expt Y) (j₂ w))).im = 0 ∧ 0 ≤ (inner ℂ (j₂ w) (π₂.π (T.expt Y) (j₂ w))).re) → (∀ x y u w : E, MeasureTheory.Integrable (fun g => inner ℂ (j₁ x) (π₁.π g (j₁ y)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ w)))) T.haar ∧ ∫ g, inner ℂ (j₁ x) (π₁.π g (j₁ y)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ w))) ∂T.haar = 0) → j₁ = 0 := by
  first | exact @GlobalTheory.PosTrace.eq_zero_of_pos_of_orth | exact GlobalTheory.PosTrace.eq_zero_of_pos_of_orth | (intros; apply GlobalTheory.PosTrace.eq_zero_of_pos_of_orth <;> assumption)
