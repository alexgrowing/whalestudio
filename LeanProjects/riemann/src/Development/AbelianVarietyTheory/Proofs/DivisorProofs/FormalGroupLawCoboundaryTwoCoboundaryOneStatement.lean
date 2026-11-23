import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ f : MvPowerSeries (Fin d) R, cob2 μ (cob1 μ f) = subst (op μ x1 (op μ x2 x3)) f - subst (op μ (op μ x1 x2) x3) f ∧ swap (cob1 μ f) - cob1 μ f = subst (fun i => swap (μ i)) f - subst μ f ∧ (∀ c c', cob2 μ (c + c') = cob2 μ c + cob2 μ c' ∧ cob2 μ (c - c') = cob2 μ c - cob2 μ c' ∧ swap (c - c') = swap c - swap c') ∧ (∀ (r : R) c, cob2 μ (r • c) = r • cob2 μ c ∧ swap (r • c) = r • swap c) ∧ IsLaw (addLaw R d) ∧ (IsLaw μ → IsCoc μ (cob1 μ f)) := by
  first | exact @GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt | exact GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt | (intros; apply GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt <;> assumption)
