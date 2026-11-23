import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformConvolutionPowApplyMemLocalDual
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniform_convolution_pow_apply_mem_localDual : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ) (m : Ideal O), m.IsMaximal → IsLocalRing (G.dual.A n) → ∃ r : ℕ, ∀ φ : G.dual.A n, φ 1 ∈ m → ∀ s, r ≤ s → ∀ a : G.A n, (φ ^ s) a ∈ m := by
  first | exact @GlobalTheory.LocalDualNil.exists_pow_apply_mem | exact GlobalTheory.LocalDualNil.exists_pow_apply_mem | (intros; apply GlobalTheory.LocalDualNil.exists_pow_apply_mem <;> assumption)
