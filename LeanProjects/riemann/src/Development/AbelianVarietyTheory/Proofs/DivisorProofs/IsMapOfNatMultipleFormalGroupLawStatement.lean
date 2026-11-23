import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfNatMultipleFormalGroupLaw
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMapOf_natMultiple_formalGroupLaw : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ j : ℕ, c.IsMapOf c ((j : ℤ_[p]) • 𝟙 G) (nmul μ j) := by
  first | exact @GlobalTheory.Katz.Chart.isMapOf_nmul | exact GlobalTheory.Katz.Chart.isMapOf_nmul | (intros; apply GlobalTheory.Katz.Chart.isMapOf_nmul <;> assumption)
