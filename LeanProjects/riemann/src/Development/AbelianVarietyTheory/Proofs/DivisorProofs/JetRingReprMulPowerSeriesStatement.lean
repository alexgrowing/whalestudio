import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingReprMulPowerSeries
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open GlobalTheory.LatJet
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_repr_mul_power_series : ∀ {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (F G : MvPowerSeries I ℂ) (x y : J.B), (∀ ν : Idx I n, J.b.repr x ν = ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F) → (∀ ν : Idx I n, J.b.repr y ν = ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) G) → ∀ ν : Idx I n, J.b.repr (x * y) ν = ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) (F * G) := by
  first | exact @GlobalTheory.JetMul.reprMul | exact GlobalTheory.JetMul.reprMul | (intros; apply GlobalTheory.JetMul.reprMul <;> assumption)
