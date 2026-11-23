import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleAdditiveEqCoboundaryAdd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricCocycle_additive_eq_coboundary_add : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R), IsCoc (addLaw R d) c → constantCoeff c = 0 → ∃ b : MvPowerSeries (Fin d) R, c = cob1 (addLaw R d) b + ∑ m : Fin d, at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (Pi.single m (X (Sum.inr m))) := by
  first | exact @GlobalTheory.symmetricCocycle_additive_eq_coboundary_add_alt | exact GlobalTheory.symmetricCocycle_additive_eq_coboundary_add_alt | (intros; apply GlobalTheory.symmetricCocycle_additive_eq_coboundary_add_alt <;> assumption)
