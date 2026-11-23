import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianModelsConjUnitaryDifferByNorm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianModels_conj_unitary_differ_by_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x x' : B.A), Q.Separable → Fits w e B Q u → ∀ γ y : GLw n w, y ∈ UL n w → IsModel w e B u x γ → IsModel w e B u x' (y⁻¹ * γ * y) → ∃ c : B.Aˣ, x' = x * ((c : B.A) * B.σ (c : B.A)) := by
  first | exact @GlobalTheory.KapLat.model_conj_norm | exact GlobalTheory.KapLat.model_conj_norm | (intros; apply GlobalTheory.KapLat.model_conj_norm <;> assumption)
