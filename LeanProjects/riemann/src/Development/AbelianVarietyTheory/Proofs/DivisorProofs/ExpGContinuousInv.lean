import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem expG_continuous_inv : ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), inG ε Z →
    Continuous (fun t : ℝ => expG ε Z t) ∧
      ∀ t : ℝ, toM (expG ε Z t)⁻¹ = NormedSpace.exp (-((t : ℂ) • Z)) := by
  intro n ε Z hZ
  refine ⟨(Formalism.REAL.group_exponential_facts n ε Z hZ).2.2.1, fun t => ?_⟩
  have hmul : toM (expG ε Z t) * NormedSpace.exp (-((t : ℂ) • Z)) = 1 := by
    rw [Formalism.REAL.toM_expG ε Z t hZ]
    have h := Formalism.REAL.one_parameter_subgroup_holds n Z t (-t)
    have e : ((-t : ℝ) : ℂ) • Z = -((t : ℂ) • Z) := by push_cast; rw [neg_smul]
    rw [e, add_neg_cancel] at h
    simpa using h.symm
  exact Units.inv_eq_of_mul_eq_one_right hmul

end GlobalTheory
