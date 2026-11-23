import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermWeierstrassPreparation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

theorem polynomial_dvd_of_eval_eq_mul_near_roots {U : Set ℂ} (hU : IsOpen U) :
    ∀ (n : ℕ) (W P : ℂ[X]) (g : ℂ → ℂ), W.Monic → W.natDegree = n → ContinuousOn g U →
      (∀ t ∈ U, P.eval t = g t * W.eval t) → (∀ t, W.IsRoot t → t ∈ U) → W ∣ P := by
  intro n
  induction n with
  | zero =>
    intro W P g hW hn _ _ _
    rw [hW.natDegree_eq_zero.1 hn]
    exact one_dvd P
  | succ n ih =>
    intro W P g hW hn hg hPW hroots
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root W (by
      rw [degree_eq_natDegree hW.ne_zero, hn]; exact_mod_cast Nat.succ_ne_zero n)
    have hαU : α ∈ U := hroots α hα
    have hPα : P.IsRoot α := by
      show P.eval α = 0
      rw [hPW α hαU, show W.eval α = 0 from hα, mul_zero]
    have hW₁ : (X - C α) * (W /ₘ (X - C α)) = W := mul_divByMonic_eq_iff_isRoot.2 hα
    have hP₁ : (X - C α) * (P /ₘ (X - C α)) = P := mul_divByMonic_eq_iff_isRoot.2 hPα
    have hW₁m : (W /ₘ (X - C α)).Monic := (monic_X_sub_C α).of_mul_monic_left (by rw [hW₁]; exact hW)
    have hW₁n : (W /ₘ (X - C α)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C α), hn, natDegree_X_sub_C]; rfl
    have hcont : ContinuousOn (fun t => g t * (W /ₘ (X - C α)).eval t) U :=
      hg.mul (W /ₘ (X - C α)).continuous.continuousOn
    have hoff : ∀ s ∈ U, s ≠ α → (P /ₘ (X - C α)).eval s = g s * (W /ₘ (X - C α)).eval s := by
      intro s hsU hs
      have h := hPW s hsU
      rw [← hP₁, ← hW₁, eval_mul, eval_mul] at h
      have hne : (X - C α).eval s ≠ 0 := by
        simp only [eval_sub, eval_X, eval_C]; exact sub_ne_zero.2 hs
      exact mul_left_cancel₀ hne (by rw [h]; ring)
    have hP₁eq : ∀ t ∈ U, (P /ₘ (X - C α)).eval t = g t * (W /ₘ (X - C α)).eval t := by
      intro t ht
      by_cases htα : t = α
      · have h1 : Tendsto (fun s => (P /ₘ (X - C α)).eval s) (𝓝[≠] t) (𝓝 ((P /ₘ (X - C α)).eval t)) :=
          (P /ₘ (X - C α)).continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        have h2 : Tendsto (fun s => g s * (W /ₘ (X - C α)).eval s) (𝓝[≠] t)
            (𝓝 (g t * (W /ₘ (X - C α)).eval t)) :=
          (hcont.continuousAt (hU.mem_nhds ht)).tendsto.mono_left nhdsWithin_le_nhds
        refine tendsto_nhds_unique (h1.congr' ?_) h2
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds ht)] with s hs hsU
        exact hoff s hsU (htα ▸ hs)
      · exact hoff t ht htα
    have hdvd := ih _ _ g hW₁m hW₁n hg hP₁eq (fun t ht => hroots t (by
      rw [← hW₁]; show ((X - C α) * (W /ₘ (X - C α))).eval t = 0
      rw [eval_mul, show (W /ₘ (X - C α)).eval t = 0 from ht, mul_zero]))
    rw [← hW₁, ← hP₁]
    exact mul_dvd_mul_left _ hdvd

theorem norm_lt_of_monic_root_small_coeffs {d : ℕ} (b : Fin d → ℂ) {r η : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hη : (d : ℝ) * η < r ^ d) (hb : ∀ j, ‖b j‖ ≤ η) (t : ℂ)
    (ht : t ^ d + ∑ j : Fin d, b j * t ^ (j : ℕ) = 0) : ‖t‖ < r := by
  by_contra h
  push Not at h
  have hT : 0 < ‖t‖ ^ d := pow_pos (lt_of_lt_of_le hr0 h) d
  have hR : 0 < r ^ d := pow_pos hr0 d
  have htd : t ^ d = -∑ j : Fin d, b j * t ^ (j : ℕ) := eq_neg_of_add_eq_zero_left ht
  have hsum : ‖t‖ ^ d ≤ ∑ _j : Fin d, η * (‖t‖ ^ d / r ^ d) := by
    calc ‖t‖ ^ d = ‖t ^ d‖ := (norm_pow _ _).symm
      _ = ‖∑ j : Fin d, b j * t ^ (j : ℕ)‖ := by rw [htd, norm_neg]
      _ ≤ ∑ j : Fin d, ‖b j * t ^ (j : ℕ)‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul, norm_pow]
          refine mul_le_mul (hb j) ?_ (by positivity) (le_trans (norm_nonneg _) (hb j))
          rw [le_div_iff₀ hR]
          calc ‖t‖ ^ (j : ℕ) * r ^ d ≤ ‖t‖ ^ (j : ℕ) * r ^ (d - j) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1 (Nat.sub_le d j)) (by positivity)
            _ ≤ ‖t‖ ^ (j : ℕ) * ‖t‖ ^ (d - j) := by gcongr
            _ = ‖t‖ ^ d := by rw [← pow_add, Nat.add_sub_cancel' j.2.le]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hlt : (d : ℝ) * (η * (‖t‖ ^ d / r ^ d)) < ‖t‖ ^ d := by
    rw [show (d : ℝ) * (η * (‖t‖ ^ d / r ^ d)) = ((d : ℝ) * η / r ^ d) * ‖t‖ ^ d by ring]
    exact mul_lt_of_lt_one_left hT ((div_lt_one hR).2 hη)
  linarith

theorem continuous_pointWithLast {σ : Type} (z : σ → ℂ) : Continuous (fun t : ℂ => pointWithLast z t) := by
  refine continuous_pi fun o => ?_
  cases o with
  | none => exact continuous_id
  | some i => exact continuous_const

theorem weierstrass_remainder_eq_zero {σ : Type} [Fintype σ] {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, ContinuousAt (c j) 0) (hc0 : ∀ j, c j 0 = 0) (a : Fin d → (σ → ℂ) → ℂ)
    (q : (Option σ → ℂ) → ℂ) (hq : AnalyticAt ℂ q 0)
    (h : ∀ᶠ x in 𝓝 (0 : Option σ → ℂ),
      ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ) = q x * weierstrassPolynomial c x) :
    ∀ j, ∀ᶠ z in 𝓝 (0 : σ → ℂ), a j z = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h.and hq.eventually_analyticAt)
  have hr0 : 0 < min ε 1 := lt_min hε one_pos
  have hrε : min ε 1 ≤ ε := min_le_left _ _
  have hR : 0 < (min ε 1) ^ d := pow_pos hr0 d
  have hηpos : 0 < (min ε 1) ^ d / (d + 1) := by positivity
  have hη : (d : ℝ) * ((min ε 1) ^ d / (d + 1)) < (min ε 1) ^ d := by
    rw [show (d : ℝ) * ((min ε 1) ^ d / (d + 1)) = (min ε 1) ^ d * (d / (d + 1)) by ring]
    exact mul_lt_of_lt_one_right hR ((div_lt_one (by positivity)).2 (by linarith))
  have hsmall : ∀ᶠ z in 𝓝 (0 : σ → ℂ), ‖z‖ < min ε 1 ∧ ∀ j, ‖c j z‖ ≤ (min ε 1) ^ d / (d + 1) := by
    refine ((continuous_norm.tendsto' (0 : σ → ℂ) 0 norm_zero).eventually (eventually_lt_nhds hr0)).and
      (Filter.eventually_all.2 fun j => ?_)
    have ht : Tendsto (fun z => ‖c j z‖) (𝓝 (0 : σ → ℂ)) (𝓝 0) := by
      simpa [hc0 j] using (hc j).norm.tendsto
    exact (ht.eventually (eventually_lt_nhds hηpos)).mono fun z hz => hz.le
  intro j
  filter_upwards [hsmall] with z hz
  obtain ⟨hzr, hcz⟩ := hz
  have hpt : ∀ t : ℂ, ‖t‖ < min ε 1 → pointWithLast z t ∈ Metric.ball (0 : Option σ → ℂ) ε := by
    intro t ht
    rw [mem_ball_zero_iff, pi_norm_lt_iff hε]
    intro o
    cases o with
    | none => exact lt_of_lt_of_le ht hrε
    | some i => exact lt_of_le_of_lt (norm_le_pi_norm z i) (lt_of_lt_of_le hzr hrε)
  have hdeg : (∑ i : Fin d, C (c i z) * X ^ (i : ℕ)).degree < (d : WithBot ℕ) := degree_sum_fin_lt _
  have hWm : (X ^ d + ∑ i : Fin d, C (c i z) * X ^ (i : ℕ)).Monic := monic_X_pow_add hdeg
  have hWn : (X ^ d + ∑ i : Fin d, C (c i z) * X ^ (i : ℕ)).natDegree = d := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have hevW : ∀ t : ℂ, (X ^ d + ∑ i : Fin d, C (c i z) * X ^ (i : ℕ)).eval t =
      weierstrassPolynomial c (pointWithLast z t) := by
    intro t
    simp only [eval_add, eval_pow, eval_X, eval_finset_sum, eval_mul, eval_C, weierstrassPolynomial]
    rfl
  have hevP : ∀ t : ℂ, (∑ i : Fin d, C (a i z) * X ^ (i : ℕ)).eval t =
      ∑ i : Fin d, a i (fun k => pointWithLast z t (some k)) * pointWithLast z t none ^ (i : ℕ) := by
    intro t
    simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
    rfl
  have hdvd := polynomial_dvd_of_eval_eq_mul_near_roots (Metric.isOpen_ball (x := (0 : ℂ)) (ε := min ε 1)) d
    _ (∑ i : Fin d, C (a i z) * X ^ (i : ℕ)) (fun t => q (pointWithLast z t)) hWm hWn
    (fun t ht => ((hball _ (hpt t (mem_ball_zero_iff.1 ht))).2.continuousAt.comp
      (continuous_pointWithLast z).continuousAt).continuousWithinAt)
    (fun t ht => by
      rw [hevP, hevW]
      exact (hball _ (hpt t (mem_ball_zero_iff.1 ht))).1)
    (fun t ht => by
      rw [mem_ball_zero_iff]
      refine norm_lt_of_monic_root_small_coeffs (fun i => c i z) hr0 (min_le_right _ _) hη hcz t ?_
      have h0 : (X ^ d + ∑ i : Fin d, C (c i z) * X ^ (i : ℕ)).eval t = 0 := ht
      simpa only [eval_add, eval_pow, eval_X, eval_finset_sum, eval_mul, eval_C] using h0)
  have hP0 : (∑ i : Fin d, C (a i z) * X ^ (i : ℕ)) = 0 :=
    eq_zero_of_dvd_of_degree_lt hdvd (by rw [degree_eq_natDegree hWm.ne_zero, hWn]; exact degree_sum_fin_lt _)
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff (j : ℕ)) hP0
  simpa [finset_sum_coeff, coeff_C_mul_X_pow, Fin.val_inj] using hcoeff

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
