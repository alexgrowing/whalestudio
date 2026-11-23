import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSGInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSWeil

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.NIS

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.FSW

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

theorem be_equiv_of_int {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN : Measure (Mt k r)} {σ : Mx k r → (H →L[ℂ] H)}
    (hG : Cv.GrpF k r z) (hσ : Cv.SigU σ) (hπ : Cv.PiU z π) (hψ : Cv.PsiF k r z c) (hM : Cv.MeasF z π μW μN)
    {w v : H} (hint : Integrable (beF z c π σ w v) (μW.prod μN))
    {h m : Mx k r} (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) :
    be z c π μW μN σ (σ (h * m) w) v = (psi k r z c m • π h).comp (be z c π μW μN σ w v) := by
  have hT := hM.2.1 h hh m hm
  let L : (Wp →L[ℂ] Wp) →L[ℂ] (Wp →L[ℂ] Wp) :=
    ContinuousLinearMap.compL ℂ Wp Wp Wp (psi k r z c m • π h)
  have key : ∀ᵐ p ∂(μW.prod μN), beF z c π σ (σ (h * m) w) v p = L (beF z c π σ w v (Cv.tEq h m p)) := by
    filter_upwards [hM.1] with p hp
    exact Cv.beF_tEq z c π σ hG hσ hπ hψ h m hh hm w v p hp
  have hint2 : Integrable (fun p => beF z c π σ w v (Cv.tEq h m p)) (μW.prod μN) :=
    hT.integrable_comp_of_integrable hint
  have hmap : ∫ p, beF z c π σ w v (Cv.tEq h m p) ∂(μW.prod μN) = be z c π μW μN σ w v := by
    rw [← integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hint.aestronglyMeasurable),
      hT.map_eq]
    rfl
  show ∫ p, beF z c π σ (σ (h * m) w) v p ∂(μW.prod μN) = L (be z c π μW μN σ w v)
  rw [integral_congr_ae key, L.integral_comp_comm hint2, hmap]

def evL (ξ : Wp) : (Wp →L[ℂ] Wp) →L[ℂ] ℂ :=
  (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ Wp ξ)

theorem evL_apply (ξ : Wp) (B : Wp →L[ℂ] Wp) : evL ξ B = ⟪ξ, B ξ⟫_ℂ := rfl

def kx (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (ξ : Wp) (p : Mt k r × Mt k r) : ℂ :=
  psi k r z c (Matrix.of p.2) * star ⟪ξ, π (Matrix.of p.1)⁻¹ ξ⟫_ℂ

def Fx (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (u v : H) (ξ : Wp) (y : Mx k r) : ℂ :=
  ⟪v, σ y u⟫_ℂ * star ⟪ξ, Aop z c π μW μN σ u v y ξ⟫_ℂ

theorem star_ev_be {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN : Measure (Mt k r)} {σ : Mx k r → (H →L[ℂ] H)} {w' v : H}
    (hint : Integrable (beF z c π σ w' v) (μW.prod μN)) (ξ : Wp) :
    star ⟪ξ, be z c π μW μN σ w' v ξ⟫_ℂ = ∫ p, star ⟪v, σ (sM p) w'⟫_ℂ * kx z c π ξ p ∂(μW.prod μN) := by
  have e1 : ⟪ξ, be z c π μW μN σ w' v ξ⟫_ℂ = ∫ p, evL ξ (beF z c π σ w' v p) ∂(μW.prod μN) := by
    rw [(evL ξ).integral_comp_comm hint, evL_apply]
    rfl
  rw [e1]
  have e2 := integral_conj (μ := μW.prod μN) (f := fun p => evL ξ (beF z c π σ w' v p))
  simp only [starRingEnd_apply] at e2
  rw [← e2]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [evL_apply, beF, kx, sM, _root_.smul_apply, inner_smul_right, star_mul', star_star]
  ring

theorem norm_kx_le {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} (hGr : Cv.GrpF k r z)
    (hPi : Cv.PiU z π) (ξ : Wp) {p : Mt k r × Mt k r} (hp : Matrix.of p.1 ∈ UWset k r z) :
    ‖kx z c π ξ p‖ ≤ ‖ξ‖ ^ 2 := by
  unfold kx
  rw [norm_mul, Cv.norm_psi, one_mul, norm_star]
  calc ‖⟪ξ, π (Matrix.of p.1)⁻¹ ξ⟫_ℂ‖ ≤ ‖ξ‖ * ‖π (Matrix.of p.1)⁻¹ ξ‖ := norm_inner_le_norm _ _
    _ = ‖ξ‖ ^ 2 := by rw [hPi.2.2 _ (hGr.2.2.1 _ hp)]; ring

theorem kx_aesm {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN : Measure (Mt k r)} [SFinite μN] (hM : Cv.MeasF z π μW μN) (ξ : Wp) :
    AEStronglyMeasurable (kx z c π ξ) (μW.prod μN) := by
  have hc1 : Continuous (fun p : Mt k r × Mt k r => psi k r z c (Matrix.of p.2)) :=
    (Cv.psi_cont z c).comp continuous_snd
  have h1 : AEStronglyMeasurable (fun p : Mt k r × Mt k r => psi k r z c (Matrix.of p.2)) (μW.prod μN) :=
    hc1.aestronglyMeasurable
  have hc : Continuous (fun B : Wp →L[ℂ] Wp => star ⟪ξ, B ξ⟫_ℂ) :=
    continuous_star.comp (evL ξ).continuous
  have h2 : AEStronglyMeasurable (fun p : Mt k r × Mt k r => star ⟪ξ, π (Matrix.of p.1)⁻¹ ξ⟫_ℂ) (μW.prod μN) :=
    hc.comp_aestronglyMeasurable hM.2.2.2.comp_fst
  exact h1.mul h2

end PI.WBL.NIS
