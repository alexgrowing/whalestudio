import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

theorem divAB_of_suppOK {K : Type} [Field K] {p : ℕ} {G : MvPowerSeries (Fin 2) K}
    (h : SuppOK p G) : DivAB G := by
  intro n hn
  by_contra hc
  obtain ⟨h0, h1, -⟩ := h n hc
  omega

theorem norm_lift_le_one {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} {σ : K →+* K}
    (hU : UnrOK K p σ) {a : K} (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  obtain ⟨hp, -, -, -, hσ⟩ := hU
  have h1 : ‖a ^ p‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg a) ha
  have h2 : ‖σ a - a ^ p‖ ≤ 1 :=
    (hσ a ha).trans (inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_lt.le))
  calc ‖σ a‖ = ‖(σ a - a ^ p) + a ^ p‖ := by rw [sub_add_cancel]
    _ ≤ max ‖σ a - a ^ p‖ ‖a ^ p‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le h2 h1

theorem BetaIsG_of (h0 : StepZero) (h1 : StepI) (h2 : StepII) (hH : StepH) (h3 : StepIII)
    (h4 : StepIV) (hSw : SwapRules) (hS : SimeqRules) : BetaIsG := by
  intro K _ _ _ _ p σ hU hζ F hF be hbe
  obtain ⟨G, hGs, hGbe, hG1, hG2⟩ := h0 K p σ hU hζ F hF be hbe
  have hp2 : 2 ≤ p := hU.2.1.le
  obtain ⟨hss, hsupp, hdivsw, -, -, -⟩ := hSw K p σ G 0 0 hp2
  obtain ⟨c, hc, hcG⟩ := h1 K p σ hU F hF G hGs hG1 hG2
  obtain ⟨c', hc', hcG'⟩ := h1 K p σ hU F hF (swap2 G) (hsupp hGs) hG2 (by rw [hss]; exact hG1)
  have hdG : DivAB G := divAB_of_suppOK hGs
  have hI1 := h2 K p σ hU F hF G c hdG hG1 hc hcG
  have hI2 := h2 K p σ hU F hF (swap2 G) c' (hdivsw hdG) hG2 hc' hcG'
  have hHs := hH K p σ hU F hF G (σ c) (σ c') hGs hI1 hI2
  have e1 : c + σ c' = 0 := h3 K p σ hU G c c' hc hc' hcG hHs
  have hHs' : Integral (Hser p σ (swap2 G) (σ c') (σ c)) := by
    rw [(hSw K p σ G (σ c) (σ c') hp2).2.2.2.2.2]
    exact (hSw K p σ (Hser p σ G (σ c) (σ c')) 0 0 hp2).2.2.2.1 hHs
  have e2 : c' + σ c = 0 := h3 K p σ hU (swap2 G) c' c hc' hc hcG' hHs'
  have hA : σ c' = -c := by linear_combination e1
  have hB : σ c' = -σ (σ c) := by
    rw [show c' = -σ c by linear_combination e2, map_neg]
  have hσσ : σ (σ c) = c := by linear_combination hB - hA
  rw [hA] at hHs
  have hSimG : Simeq G (Gser p c (σ c)) := h4 K p σ hU G c hdG hσσ hHs
  obtain ⟨-, hsymm, htrans, -, -⟩ := hS K (Fin 2)
  exact ⟨c, hc, hσσ, htrans _ _ _ (hsymm _ _ hGbe) hSimG⟩

theorem ThmSFull_of (hB : BetaIsG) (hK : CyclicPowerClassOfExpEquiv) (hM : MapSimeq) : ThmSFull := by
  intro K0 K _ _ _ _ _ _ _ j p ν r0 r1 _ σ hj hU hζ F hF be hbe
  obtain ⟨c, hc, hσc, hsim⟩ := hB K0 p σ hU hζ F hF be hbe
  refine ⟨c, hc, hσc, ?_⟩
  intro om oms ϖ μ U0 Φ hϖ hom hμ0 hμ hU0 hΦ0 hΦ
  have hpK : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast j p, hj]
    exact hU.2.2.1
  have hσc1 : ‖σ c‖ ≤ 1 := norm_lift_le_one hU hc
  obtain ⟨hMs, hMG⟩ := hM K0 K (Fin 2) j hj
  refine hK K p ν r0 r1 om oms (j c) (j (σ c)) ϖ μ U0 Φ (MvPowerSeries.map j be) hU.1 hpK hϖ
    hom (by rw [hj]; exact hc) (by rw [hj]; exact hσc1) hμ0 hμ hU0 hΦ0 hΦ ?_
  rw [← hMG p c (σ c)]
  exact hMs _ _ hsim

end Formalism.InvariantFactorPaths.G7
