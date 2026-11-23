import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffCob1HomogLiftBinomial
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_cob1_homog_lift_binomial : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (m : ℕ) (h : MvPowerSeries (Fin d) Q), m ≠ 0 → (∀ α : Fin d →₀ ℕ, α.degree ≠ m → coeff α h = 0) → ∀ a e : Fin d →₀ ℕ, (a + e).degree ≤ m → coeff (Finsupp.sumElim a e) (cob1 (up Q μ) h) = if a ≠ 0 ∧ e ≠ 0 then (∏ i, Nat.choose ((a + e) i) (a i) : Q) * coeff (a + e) h else 0 := by
  first | exact @GlobalTheory.CobHom.coeff_cob1_homogeneous_binomial | exact GlobalTheory.CobHom.coeff_cob1_homogeneous_binomial | (intros; apply GlobalTheory.CobHom.coeff_cob1_homogeneous_binomial <;> assumption)
