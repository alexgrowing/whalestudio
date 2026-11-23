import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjUnitaryOfSameHermitianMultiplicationModel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_unitary_of_same_hermitianMultiplicationModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ γ' : GLw n w), IsModel w e B u x γ → IsModel w e B u x γ' → ∃ y ∈ UL n w, γ' = y⁻¹ * γ * y := by
  first | exact @GlobalTheory.KapLat.models_conj | exact GlobalTheory.KapLat.models_conj | (intros; apply GlobalTheory.KapLat.models_conj <;> assumption)
