import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomNmulOfIsLaw
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHom_nmul_of_isLaw : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ k : ℕ, IsHom μ μ (nmul μ k) := by
  first | exact @GlobalTheory.NMulEndo.isHom_nmul | exact GlobalTheory.NMulEndo.isHom_nmul | (intros; apply GlobalTheory.NMulEndo.isHom_nmul <;> assumption)
