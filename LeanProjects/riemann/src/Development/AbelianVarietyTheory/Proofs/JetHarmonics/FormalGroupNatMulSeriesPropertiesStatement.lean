import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesProperties
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupNatMulSeries_properties : ∀ (R : Type) [CommRing R] (F : FormalGroup R), (∀ n, PowerSeries.constantCoeff (nMul F n) = 0 ∧ PowerSeries.coeff 1 (nMul F n) = (n : R)) ∧ nMul F 1 = PowerSeries.X ∧ (∀ i j, MvPowerSeries.subst (![nMul F i, nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries = nMul F (i + j)) ∧ (∀ i j, (nMul F i).subst (nMul F j) = nMul F (i * j)) ∧ (∀ (S : Type) [CommRing S] (φ : R →+* S) (n : ℕ), PowerSeries.map φ (nMul F n) = nMul (F.map φ) n) := by
  first | exact @GlobalTheory.ConvSer.nMul_props | exact GlobalTheory.ConvSer.nMul_props | (intros; apply GlobalTheory.ConvSer.nMul_props <;> assumption)
