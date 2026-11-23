import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements

open MvPolynomial

namespace ChowFormCompatibility

theorem chow_form_of_integral_version : ∀ (k : Type) [Field k] (N e d : ℕ) (I : Ideal (MvPolynomial (Fin N) k)) (f : MvPolynomial (Fin (e + 1) × Fin N) k), GlobalTheory.ChowHt.IsChowFormInt I e d f → GroundTheory.Heights₂.Heights.IsChowForm I (e + 1) f := by
  intro k _ N e d I f h
  refine ⟨h.ne_zero, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · exact h.dvd_of_forall_aeval_eq_zero fun u hu => hg u ((h.zero_iff u).1 hu)
  · rintro ⟨a, rfl⟩ u hu
    rw [map_mul, (h.zero_iff u).2 hu, zero_mul]

end ChowFormCompatibility
