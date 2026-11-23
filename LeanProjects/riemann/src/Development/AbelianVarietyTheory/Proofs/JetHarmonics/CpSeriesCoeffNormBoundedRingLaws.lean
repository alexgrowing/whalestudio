import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesSupNormMulPadicComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem sup_norm_laws : ∀ (q : ℕ) [Fact q.Prime], (∀ (f g : ℂ_[q]⟦X⟧) (A B : ℝ), Bd A f → Bd B g → Bd (max A B) (f + g) ∧ Bd (A * B) (f * g)) ∧ (∀ (f h : ℂ_[q]⟦X⟧) (A : ℝ), Bd A f → Bd 1 h → constantCoeff h = 0 → Bd A (f.subst h)) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bd 1 f → ‖constantCoeff f‖ = 1 → f * g = 1 → Bd 1 g) ∧ (∀ (f g : ℂ_[q]⟦X⟧) (B : ℝ), Bdd f → Bdd g → Bd B (f * g) → ∀ i j, ‖coeff i f‖ * ‖coeff j g‖ ≤ B) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bdd f → Bdd g → f * g = 1 → constantCoeff f = 1 → Bd 1 f ∧ Bd 1 g) ∧ (∀ (f v : ℂ_[q]⟦X⟧) (k : ℕ) (B : ℝ), Bd 1 v → ‖constantCoeff v‖ = 1 → Bd B (X ^ k * v * f) → Bd B f) := by
  intro q _
  have R := GlobalTheory.EvenTheta.SerRing.series_ring_laws q
  have hmul : ∀ (f g : ℂ_[q]⟦X⟧) (A B : ℝ), Bd A f → Bd B g → Bd (A * B) (f * g) :=
    fun f g A B hf hg => R.2.2.2.2.2.2 f g A B hf hg
  have hinv : ∀ f : ℂ_[q]⟦X⟧, Bd 1 f → ‖constantCoeff f‖ = 1 → Bd 1 f⁻¹ :=
    fun f hf h0 => R.2.2.2.2.1 f hf h0
  have hinv' : ∀ (f g : ℂ_[q]⟦X⟧), Bd 1 f → ‖constantCoeff f‖ = 1 → f * g = 1 → Bd 1 g := by
    intro f g hf h0 hfg
    have hc : constantCoeff f ≠ 0 := by
      intro h
      rw [h, norm_zero] at h0
      exact zero_ne_one h0
    have hgf : g = f⁻¹ := by
      rw [PowerSeries.eq_inv_iff_mul_eq_one hc, mul_comm]
      exact hfg
    rw [hgf]
    exact hinv f hf h0
  have hgauss : ∀ (f g : ℂ_[q]⟦X⟧) (B : ℝ), Bdd f → Bdd g → Bd B (f * g) →
      ∀ i j, ‖coeff i f‖ * ‖coeff j g‖ ≤ B :=
    fun f g B hf hg hB => GlobalTheory.EvenTheta.sup_norm_mul_padicComplex q f g B hf hg hB
  refine ⟨fun f g A B hf hg => ⟨fun n => GlobalTheory.EvenTheta.SerRing.norm_coeff_add_le f g A B hf hg n,
    hmul f g A B hf hg⟩, fun f h A hf hh h0 => R.2.2.2.2.2.1 f h A hf hh h0, hinv', hgauss, ?_, ?_⟩
  · intro f g hf hg hfg h1
    have hg0 : constantCoeff g = 1 := by
      have hc := congrArg constantCoeff hfg
      rw [map_mul, h1, one_mul, map_one] at hc
      exact hc
    have hB : Bd 1 (f * g) := by
      rw [hfg]
      intro n
      rw [coeff_one]
      split_ifs <;> simp
    have H := hgauss f g 1 hf hg hB
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have hi := H i 0
      rwa [coeff_zero_eq_constantCoeff_apply, hg0, norm_one, mul_one] at hi
    · have hj := H 0 j
      rwa [coeff_zero_eq_constantCoeff_apply, h1, norm_one, one_mul] at hj
  · intro f v k B hv h0 hB
    have hw : Bd B (v * f) := by
      intro m
      have hm := hB (m + k)
      rwa [mul_assoc, coeff_X_pow_mul] at hm
    have hc : constantCoeff v ≠ 0 := by
      intro h
      rw [h, norm_zero] at h0
      exact zero_ne_one h0
    have hvf := hmul v⁻¹ (v * f) 1 B (hinv v hv h0) hw
    rwa [← mul_assoc, PowerSeries.inv_mul_cancel _ hc, one_mul, one_mul] at hvf

end GlobalTheory.MomOne
