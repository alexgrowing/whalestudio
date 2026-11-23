import Mathlib
import Formalism.PeriodIntegrals.StrongApproxE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.LocSmall
import Lemmata.Cancellation.EnnrealVolumeRatioStepCancel

noncomputable section

open IsDedekindDomain NumberField

namespace PI.StrongApproxE

namespace DedekindLFunctions

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem exists_pow_le (p : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    ∃ N : ℕ, ∀ y ∈ p.asIdeal ^ N, p.valuation K (algebraMap R K y) ≤ p.valuation K (algebraMap R K r) := by
  refine ⟨(Associates.mk p.asIdeal).count (Associates.mk (Ideal.span {r})).factors, fun y hy => ?_⟩
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    p.intValuation_if_neg hr]
  exact (p.intValuation_le_pow_iff_mem y _).2 hy

theorem sa (T : Finset (HeightOneSpectrum R)) (a c : HeightOneSpectrum R → K) (hc : ∀ p ∈ T, c p ≠ 0) :
    ∃ t : K, (∀ p ∈ T, p.valuation K (t - a p) ≤ p.valuation K (c p)) ∧
      ∀ p, p ∉ T → p.valuation K t ≤ 1 := by
  first | exact Bl.VolumeRatioCancellation.goal1 .. | (apply Bl.VolumeRatioCancellation.goal1 <;> assumption) | (intros; apply Bl.VolumeRatioCancellation.goal1 <;> assumption)

end DedekindLFunctions

theorem strong_approximation_finite_places : DedSA := by
  intro F _ _ T a c hc
  exact DedekindLFunctions.sa (R := 𝓞 F) (K := F) T a c hc

end PI.StrongApproxE
