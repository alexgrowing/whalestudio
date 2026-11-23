import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotSetU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientInvariantMeasurability.MeasurableAvgS

open MeasureTheory Matrix
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.QuotUniq

open Formalism.QuantumDeterminants Formalism.MainNotions.S

def QuotUniqS : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μG μS ν ν' : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
    IsHaarOn (UH (Hpk k r)) μG → IsHaarOn (Sset k r z) μS → IsQuotMeas μG μS ν → IsQuotMeas μG μS ν' →
    ∀ F : Mt k r → ENNReal, Measurable F →
      (∀ s ∈ Sset k r z, ∀ x : Mt k r, Matrix.of x ∈ UH (Hpk k r) → F (fun i j => (s * Matrix.of x) i j) = F x) →
      ∫⁻ x, F x ∂ν = ∫⁻ x, F x ∂ν'

def QuotLeftNorm : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μG μS ν : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
    IsHaarOn (UH (Hpk k r)) μG → IsHaarOn (Sset k r z) μS → IsQuotMeas μG μS ν →
    ∀ t ∈ UH (Hpk k r), (∀ s ∈ Sset k r z, t * s * t⁻¹ ∈ Sset k r z ∧ t⁻¹ * s * t ∈ Sset k r z) →
      μS.map (fun x => fun i j => (t * Matrix.of x * t⁻¹) i j) = μS →
      ∀ F : Mt k r → ENNReal, Measurable F →
        (∀ s ∈ Sset k r z, ∀ x : Mt k r, Matrix.of x ∈ UH (Hpk k r) → F (fun i j => (s * Matrix.of x) i j) = F x) →
        ∫⁻ x, F (fun i j => (t * Matrix.of x) i j) ∂ν = ∫⁻ x, F x ∂ν

section General

open PI PI.QuotInvW

variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν ν' : Measure (MtM m)}

theorem lintegral_eq_weight (h : QuotientSetting G S μG μS ν) {ρ : MtM m → ℝ≥0∞} (hρm : Measurable ρ)
    (hρ0 : ∀ x, ρ x ≠ 0) (hρi : ∫⁻ x, ρ x ∂μG ≠ ⊤) {F : MtM m → ℝ≥0∞} (hF : Measurable F)
    (hFi : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F (mm s x) = F x) :
    ∫⁻ x, F x ∂ν = ∫⁻ x, F x * (avgS μS ρ x)⁻¹ * ρ x ∂μG := by
  have : SigmaFinite μS := h.2.2.2.2.1.1
  have hcm : Measurable (avgS μS ρ) := measurable_avgS hρm
  have hH : Measurable (fun x => F x * (avgS μS ρ x)⁻¹) := hF.mul hcm.inv
  have hHi : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G →
      F (mm s x) * (avgS μS ρ (mm s x))⁻¹ = F x * (avgS μS ρ x)⁻¹ := by
    intro s hs x hx
    rw [hFi s hs x hx, avgS_mm h hρm (t := s) hs x]
  have hw := weil_inv h hH hρm hHi
  have hint : ∫⁻ x, avgS μS ρ x ∂ν ≠ ⊤ := by
    have := weil h hρm
    rw [this] at hρi
    exact hρi
  have hfin : ∀ᵐ x ∂ν, avgS μS ρ x < ⊤ := ae_lt_top hcm hint
  rw [hw]
  refine lintegral_congr_ae ?_
  filter_upwards [hfin] with x hx
  change F x = F x * (avgS μS ρ x)⁻¹ * avgS μS ρ x
  rw [mul_assoc, ENNReal.inv_mul_cancel (avgS_ne_zero h hρm hρ0 x) hx.ne, mul_one]

theorem lintegral_eq_of_quot (h : QuotientSetting G S μG μS ν) (h' : QuotientSetting G S μG μS ν')
    {F : MtM m → ℝ≥0∞} (hF : Measurable F)
    (hFi : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F (mm s x) = F x) :
    ∫⁻ x, F x ∂ν = ∫⁻ x, F x ∂ν' := by
  have : SigmaFinite μG := h.2.2.2.1.1
  obtain ⟨w, hw0, hwm, hwi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  have hρm : Measurable (fun x => (w x : ℝ≥0∞)) := hwm.coe_nnreal_ennreal
  have hρ0 : ∀ x, (w x : ℝ≥0∞) ≠ 0 := fun x => by simp [(hw0 x).ne']
  have hρi : ∫⁻ x, (w x : ℝ≥0∞) ∂μG ≠ ⊤ := (hwi.trans ENNReal.one_lt_top).ne
  rw [lintegral_eq_weight h hρm hρ0 hρi hF hFi, lintegral_eq_weight h' hρm hρ0 hρi hF hFi]

theorem isQuotM_map_left (h : QuotientSetting G S μG μS ν) {t : Matrix (Fin m) (Fin m) ℂ} (ht : t ∈ G)
    (hμ : μS.map (fun x : MtM m => fun i j => (t * Matrix.of x * t⁻¹) i j) = μS) :
    IsQuotM μG μS (ν.map (fun x : MtM m => fun i j => (t * Matrix.of x) i j)) := by
  intro f hf
  have : SigmaFinite μS := h.2.2.2.2.1.1
  set L : MtM m → MtM m := fun x => fun i j => (t * Matrix.of x) i j with hLdef
  set C : MtM m → MtM m := fun x => fun i j => (t * Matrix.of x * t⁻¹) i j with hCdef
  have hL : Measurable L := measurable_mm_right (m := m) t
  have hC : Measurable C :=
    (measurable_mm_left (m := m) (t⁻¹ : Matrix (Fin m) (Fin m) ℂ)).comp (measurable_mm_right (m := m) t)
  have hG' : μG.map L = μG := h.2.2.2.1.2.2.2 t ht
  have hinv : t⁻¹ * t = 1 := inv_mul_of h.1 ht
  have hA : Measurable (fun y : MtM m => ∫⁻ s, f (mm s y) ∂μS) := measurable_avgS hf
  have key : ∀ s x : MtM m, L (mm s x) = mm (C s) (L x) := by
    intro s x
    have e : t * Matrix.of s * t⁻¹ * (t * Matrix.of x) = t * (Matrix.of s * Matrix.of x) := by
      rw [Matrix.mul_assoc (t * Matrix.of s) t⁻¹, ← Matrix.mul_assoc t⁻¹ t, hinv, Matrix.one_mul,
        Matrix.mul_assoc]
    funext i j
    change (t * (Matrix.of s * Matrix.of x)) i j = (t * Matrix.of s * t⁻¹ * (t * Matrix.of x)) i j
    rw [e]
  calc ∫⁻ x, f x ∂μG = ∫⁻ x, f x ∂(μG.map L) := by rw [hG']
    _ = ∫⁻ x, f (L x) ∂μG := lintegral_map hf hL
    _ = ∫⁻ x, (∫⁻ s, f (L (mm s x)) ∂μS) ∂ν := weil h (hf.comp hL)
    _ = ∫⁻ x, (∫⁻ s, f (mm s (L x)) ∂μS) ∂ν := by
        refine lintegral_congr fun x => ?_
        calc ∫⁻ s, f (L (mm s x)) ∂μS = ∫⁻ s, f (mm (C s) (L x)) ∂μS := by
              refine lintegral_congr fun s => ?_
              rw [key s x]
          _ = ∫⁻ s, f (mm s (L x)) ∂(μS.map C) :=
              (lintegral_map (hf.comp (measurable_mm_left (L x))) hC).symm
          _ = ∫⁻ s, f (mm s (L x)) ∂μS := by rw [hμ]
    _ = ∫⁻ y, (∫⁻ s, f (mm s y) ∂μS) ∂(ν.map L) := (lintegral_map hA hL).symm

end General

theorem quotLeftNorm : QuotLeftNorm := by
  intro k r z μG μS ν hz hT hG hS hq t ht hN hμS F hF hFS
  obtain ⟨h1, h2, h3, h4, h5⟩ := quotient_measure_unitary_group k r z hz hT
  have hset : PI.QuotientSetting (UH (Hpk k r)) (Sset k r z) μG μS ν :=
    ⟨h1, h2, h3, hG, hS, h4 μG hG, h5 μS hS, hq⟩
  have hq1 := isQuotM_map_left hset ht hμS
  have hL : Measurable (fun x : Mt k r => (fun i j => (t * Matrix.of x) i j : Mt k r)) :=
    PI.QuotInvW.measurable_mm_right (m := 2 * r + k + 1) t
  have e := lintegral_eq_of_quot ⟨h1, h2, h3, hG, hS, h4 μG hG, h5 μS hS, hq1⟩ hset hF
    (fun s hs x hx => hFS s hs x hx)
  rw [lintegral_map hF hL] at e
  exact e

end Formalism.MainNotions.S.Pv.QuotUniq

end
