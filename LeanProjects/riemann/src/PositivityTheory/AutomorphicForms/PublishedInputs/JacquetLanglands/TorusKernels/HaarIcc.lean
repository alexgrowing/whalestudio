import Mathlib

noncomputable section
open MeasureTheory

namespace UpperTheory.Esk.UnipotentIntegrandLemmas

theorem haar_Icc (m : Measure ℝ) (hinv : ∀ c : ℝ, ∀ S : Set ℝ, MeasurableSet S → m ((fun x => c + x) ⁻¹' S) = m S)
    (a0 ℓ : ℝ) (hℓ : 0 < ℓ) (hfin : m (Set.Icc a0 (a0 + ℓ)) ≠ ⊤) :
    ∃ R : ℝ, ∀ a c : ℝ, a ≤ c → (m (Set.Icc a c)).toReal = R * (c - a) := by
  have hI : m.IsAddLeftInvariant := ⟨fun c => Measure.ext fun S hS => by
    rw [Measure.map_apply (measurable_const_add c) hS]; exact hinv c S hS⟩
  have hfin' : ∀ a, m (Set.Icc a (a + ℓ)) < ⊤ := by
    intro a
    have h := hinv (a0 - a) (Set.Icc a0 (a0 + ℓ)) measurableSet_Icc
    rw [Set.preimage_const_add_Icc] at h
    have e1 : a0 - (a0 - a) = a := by ring
    have e2 : a0 + ℓ - (a0 - a) = a + ℓ := by ring
    rw [e1, e2] at h
    rw [h]; exact lt_top_iff_ne_top.2 hfin
  have hL : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Set.Icc (x - ℓ / 2) (x - ℓ / 2 + ℓ),
    Icc_mem_nhds (by linarith) (by linarith), hfin' _⟩⟩
  have hm := Measure.isAddLeftInvariant_eq_smul m (volume : Measure ℝ)
  refine ⟨(Measure.addHaarScalarFactor m volume : ℝ), fun a c hac => ?_⟩
  have h2 := congrArg (fun μ : Measure ℝ => μ (Set.Icc a c)) hm
  rw [h2, Measure.smul_apply, Real.volume_Icc, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ENNReal.toReal_ofReal (sub_nonneg.2 hac)]

end UpperTheory.Esk.UnipotentIntegrandLemmas
