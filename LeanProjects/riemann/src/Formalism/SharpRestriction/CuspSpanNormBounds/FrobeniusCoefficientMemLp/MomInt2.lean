import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomBf
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomTwMeas
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.QuotUniq

open Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.LowestKTypeMultiplicity

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem bessel_smul {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (hB : IsBesselMapSm z ψ σ π B) (α : ℂ) : IsBesselMapSm z ψ σ π (fun v => α • B v) := by
  obtain ⟨h1, h2, h3, C, Ws, hWs, hbd⟩ := hB
  refine ⟨fun v hv w hw => ?_, fun a v hv => ?_, fun h hh m hm v hv => ?_, ‖α‖ * C, Ws, hWs, fun v hv => ?_⟩
  · show α • B (v + w) = α • B v + α • B w
    rw [h1 v hv w hw, smul_add]
  · show α • B (a • v) = a • (α • B v)
    rw [h2 a v hv, smul_comm]
  · show α • B (σ (h * m) v) = ψ m • π h (α • B v)
    rw [h3 h hh m hm v hv, map_smul, smul_comm]
  · show ‖α • B v‖ ≤ ‖α‖ * C * _
    rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbd v hv) (norm_nonneg _)

theorem twist_lintegral (hLN : Formalism.MainNotions.S.Pv.QuotUniq.QuotLeftNorm)
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UH (Hpk k r)) σ)
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (c : ℂ)
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hπ : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) {B : H → Wp} (hB : IsBesselMapSm z (psi k r z c) σ π B)
    {μG μW ν : Measure (Mt k r)} (κN : ℝ≥0∞) (hG : IsHaarOn (UH (Hpk k r)) μG) (hW : IsHaarOn (UWset k r z) μW)
    (hS : IsHaarOn (Sset k r z) (muS μW (haarLie (Nset k r) κN)))
    (hq : IsQuotMeas μG (muS μW (haarLie (Nset k r) κN)) ν) {u : H} (hu : IsSmoothVec (k := k) (r := r) σ u)
    {Φ0 : (Fin (r + 1) → ℝ) → ℝ≥0∞} (hΦ0 : Measurable Φ0) :
    ∫⁻ x, Φ0 (fun a => lA k r z (Matrix.of x) a) * (‖B (σ (twT k r) (σ (Matrix.of x) u))‖₊ : ℝ≥0∞) ^ 2 ∂ν =
      ∫⁻ x, Φ0 (fun a => lA k r z (Matrix.of x) a) * (‖B (σ (Matrix.of x) u)‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
  have hconc := Formalism.MainNotions.BesselShellMomentBounds.quot_conc z μG _ ν hG hS hq
  have hae : ∀ᵐ x ∂ν, Matrix.of x ∈ UH (Hpk k r) := by rw [ae_iff]; exact hconc
  have hFm := Fu_meas hσ hB hu hΦ0
  have hmap := map_muS_cjM (z := z) κN hW
  have key : ∫⁻ x, Fu σ z B Φ0 u (fun i j => (twT k r * Matrix.of x) i j) ∂ν = ∫⁻ x, Fu σ z B Φ0 u x ∂ν :=
    hLN k r z μG (muS μW (haarLie (Nset k r) κN)) ν hz hT hG hS hq (twT k r) twT_mem_UH
      (fun s hs => twT_conj_S hs) hmap (Fu σ z B Φ0 u) hFm (Fu_leftS laLeftS_proved hσ hz c hπ hB Φ0 hu)
  have E1 : ∫⁻ x, Φ0 (fun a => lA k r z (Matrix.of x) a) * (‖B (σ (twT k r) (σ (Matrix.of x) u))‖₊ : ℝ≥0∞) ^ 2 ∂ν =
      ∫⁻ x, Fu σ z B Φ0 u (fun i j => (twT k r * Matrix.of x) i j) ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    have hx' : Matrix.of (fun i j => (twT k r * Matrix.of x) i j) ∈ UH (Hpk k r) := WeylGroupFacts.uh_mul twT_mem_UH hx
    rw [Fu_on z B Φ0 u _ hx']
    have e0 : (Matrix.of (fun i j => (twT k r * Matrix.of x) i j) : Matrix _ _ ℂ) = twT k r * Matrix.of x := rfl
    have e1 : σ (twT k r * Matrix.of x) u = σ (twT k r) (σ (Matrix.of x) u) := by
      rw [hσ.1.2 _ twT_mem_UH _ hx]; rfl
    have e2 : (fun a => lA k r z (twT k r * Matrix.of x) a) = (fun a => lA k r z (Matrix.of x) a) :=
      funext fun a => lA_twT hz _ a
    rw [e0, e1, e2, Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq]
  have E2 : ∫⁻ x, Φ0 (fun a => lA k r z (Matrix.of x) a) * (‖B (σ (Matrix.of x) u)‖₊ : ℝ≥0∞) ^ 2 ∂ν =
      ∫⁻ x, Fu σ z B Φ0 u x ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [Fu_on z B Φ0 u x hx, Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq]
  rw [E1, E2, key]

end Formalism.MainNotions.S.Pv.Mom
