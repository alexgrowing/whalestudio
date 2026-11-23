import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FrequencySumBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicThreshold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bExpHolds

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

private lemma le_max_mul_exp_mul_exp_of_le_exp {N Cη c L S s T : ℝ} (hc : 0 ≤ c) (hL : 0 < L) (hS0 : 0 < S)
    (hS1 : S < 1) (hSL : S < 3 / 2 * L) (hcs : c < s) (hT : s / S ≤ T)
    (hb : N ≤ Cη * Real.exp (-4 * Real.pi * (1 - 1 / 4) * T)) :
    N ≤ max Cη 0 * Real.exp (-(Real.pi * c / L)) * Real.exp (-(3 * Real.pi / 2) * s) := by
  have hpi := Real.pi_pos
  have hs0 : 0 ≤ s := by linarith
  have h1 : s ≤ s / S := by
    rw [le_div_iff₀ hS0]
    nlinarith [mul_nonneg hs0 (sub_nonneg.2 hS1.le)]
  have h2 : c / S ≤ s / S := by
    rw [div_le_div_iff₀ hS0 hS0]
    exact mul_le_mul_of_nonneg_right hcs.le hS0.le
  have h3 : Real.pi * c / L ≤ 3 / 2 * Real.pi * (c / S) := by
    rw [mul_div_assoc', div_le_div_iff₀ hL hS0]
    nlinarith [mul_nonneg (mul_nonneg hpi.le hc) (sub_nonneg.2 hSL.le)]
  have hexp1 : Real.exp (-4 * Real.pi * (1 - 1 / 4) * T) ≤
      Real.exp (-(Real.pi * c / L)) * Real.exp (-(3 * Real.pi / 2) * s) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have k1 := mul_le_mul_of_nonneg_left hT hpi.le
    have k2 := mul_le_mul_of_nonneg_left h1 hpi.le
    have k3 := mul_le_mul_of_nonneg_left h2 hpi.le
    linarith
  calc N ≤ Cη * Real.exp (-4 * Real.pi * (1 - 1 / 4) * T) := hb
    _ ≤ max Cη 0 * Real.exp (-4 * Real.pi * (1 - 1 / 4) * T) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max Cη 0 * (Real.exp (-(Real.pi * c / L)) * Real.exp (-(3 * Real.pi / 2) * s)) :=
      mul_le_mul_of_nonneg_left hexp1 (le_max_right _ _)
    _ = _ := by ring

theorem cuspidalDecay_holds : CuspidalExponentialDecay (E := E) := by
  intro r X la P c hc hP
  simp only [Data.SSgt, Data.SS, Data.IsBddSec, Set.mem_setOf_eq] at hP
  obtain ⟨⟨⟨hsec, B, hB⟩, -⟩, hgt⟩ := hP
  have h3d := (moderateCoefficientPositivity_holds (E := E)) r X la P B 0 hsec (by
    intro x hx
    simpa only [neg_zero, Real.rpow_zero, mul_one] using hB x hx)
  obtain ⟨hnn, hdec⟩ := h3d
  obtain ⟨Cη, hCη⟩ := hdec (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨Kf, hKf⟩ := FrequencySumBounds.freq_sum_bound X la (3 * Real.pi / 2) (by positivity)
  obtain ⟨δ0, hδ0, hiso0⟩ := IsotropicThreshold.iso_threshold X
  obtain ⟨δ, hδpos, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ 3 / 2 * δ < δ0 ∧ 3 / 2 * δ < 1 :=
    ⟨min δ0 1 / 2, half_pos (lt_min hδ0 one_pos),
      by linarith [min_le_left δ0 1, lt_min hδ0 one_pos],
      by linarith [min_le_right δ0 1, lt_min hδ0 one_pos]⟩
  have hC10 : 0 ≤ max Cη 0 := le_max_right _ _
  have hK0 : 0 ≤ Kf := by simpa using hKf ∅ (by simp)
  have h2pc : 0 ≤ 2 * Real.pi * c := mul_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) hc
  refine ⟨B ^ 2 * Real.exp (2 * Real.pi * c / δ) + (max Cη 0 * Kf) ^ 2, ?_⟩
  intro x hx
  have hpn : X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
  have hnf : 0 ≤ X.nfac la x := by
    unfold Data.nfac
    exact Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  have hp0 : 0 ≤ X.pnorm la P x := by
    rw [hpn]
    exact mul_nonneg (norm_nonneg _) hnf
  have hexp : 0 < Real.exp (-2 * Real.pi * c / X.firstMinimumSq x) := Real.exp_pos _
  by_cases hL : 0 < X.firstMinimumSq x ∧ X.firstMinimumSq x < δ
  · obtain ⟨hL0, hLδ⟩ := hL
    have hLs : X.firstMinimumSq x = sInf {t | ∃ w ∈ X.Λ, w ≠ 0 ∧
        t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 w)} := rfl
    have hne : ({t | ∃ w ∈ X.Λ, w ≠ 0 ∧
        t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 w)} : Set ℝ).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      rw [hLs, h, Real.sInf_empty] at hL0
      exact lt_irrefl _ hL0
    have hlt : sInf {t | ∃ w ∈ X.Λ, w ≠ 0 ∧
        t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 w)} < 3 / 2 * X.firstMinimumSq x := by
      rw [← hLs]
      linarith
    obtain ⟨S, ⟨v, hvΛ, hv0, hSdef⟩, hS⟩ := exists_lt_of_csInf_lt hne hlt
    have hSδ0 : S < δ0 := by linarith
    have hS1 : S < 1 := by linarith
    have hherm : herm X.Gm v v = 0 := hiso0 x hx v hvΛ (by rw [← hSdef]; exact hSδ0)
    have hiso : X.IsIso v := by
      unfold Data.IsIso
      exact ⟨hvΛ, hherm, hv0⟩
    have hterm_pos : ∀ τ, 0 < X.c τ * X.maj x τ (Data.emb τ.1 v) := fun τ =>
      mul_pos (IsotropicThreshold.c_pos X τ) (Data.maj_pos (X := X) hx τ (emb_ne_zero τ.1 hv0))
    have hterm_le : ∀ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) ≤ S := fun τ => by
      rw [hSdef]
      exact Finset.single_le_sum (fun τ _ => (hterm_pos τ).le) (Finset.mem_univ τ)
    have hcond : ∀ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) ≤ 1 := fun τ => by
      linarith [hterm_le τ]
    have htt : ∀ τ, 1 / S ≤ X.tt v x τ := fun τ => by
      unfold Data.tt
      exact one_div_le_one_div_of_le (hterm_pos τ) (hterm_le τ)
    have hsum : HasSum (fun ν : X.Ψ → ℝ => X.fj la v ν P x) (P x) := by
      have h := (m3bExp_holds (E := E)) r X la P hsec v hiso x hx 0
        (by rw [EmbeddingHermitianPairs.flow_zero]; exact hx)
      simpa [EmbeddingHermitianPairs.flow_zero] using h
    have hper : ∀ ν : X.Ψ → ℝ, X.fj la v ν P x ≠ 0 →
        ‖X.fj la v ν P x‖ * X.nfac la x ≤
          max Cη 0 * Real.exp (-(Real.pi * c / X.firstMinimumSq x)) *
            Real.exp (-(3 * Real.pi / 2) * ∑ τ, ν τ) := by
      intro ν hν
      have hν0 : ∀ τ, 0 ≤ ν τ := hnn v hiso ν x hx hν
      have hνc : c < ∑ τ, ν τ := by
        by_contra h
        exact hν (hgt v hiso ν (not_lt.1 h) x hx)
      have hΨ : (Finset.univ : Finset X.Ψ).Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        rw [h, Finset.sum_empty] at hνc
        linarith
      have hSpos : 0 < S := by
        rw [hSdef]
        exact Finset.sum_pos (fun τ _ => hterm_pos τ) hΨ
      have hT : (∑ τ, ν τ) / S ≤ ∑ τ, ν τ * X.tt v x τ := by
        rw [div_eq_mul_one_div, Finset.sum_mul]
        exact Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (htt τ) (hν0 τ)
      have hb := hCη v hiso ν x hx hcond
      rw [neg_zero, Real.rpow_zero, mul_one] at hb
      exact le_max_mul_exp_mul_exp_of_le_exp hc hL0 hSpos hS1 hS hνc hT hb
    have hfin : ∀ F : Finset (X.Ψ → ℝ), ∑ ν ∈ F, ‖X.fj la v ν P x‖ * X.nfac la x ≤
        max Cη 0 * Real.exp (-(Real.pi * c / X.firstMinimumSq x)) * Kf := by
      intro F
      calc ∑ ν ∈ F, ‖X.fj la v ν P x‖ * X.nfac la x
          ≤ ∑ ν ∈ F, (if X.fj la v ν P x ≠ 0 then
              max Cη 0 * Real.exp (-(Real.pi * c / X.firstMinimumSq x)) *
                Real.exp (-(3 * Real.pi / 2) * ∑ τ, ν τ) else 0) := by
            apply Finset.sum_le_sum
            intro ν _
            split_ifs with h
            · exact hper ν h
            · simp only [not_not] at h
              simp [h]
        _ = ∑ ν ∈ F.filter (fun ν => X.fj la v ν P x ≠ 0),
              max Cη 0 * Real.exp (-(Real.pi * c / X.firstMinimumSq x)) *
                Real.exp (-(3 * Real.pi / 2) * ∑ τ, ν τ) := by
            rw [Finset.sum_filter]
        _ = max Cη 0 * Real.exp (-(Real.pi * c / X.firstMinimumSq x)) *
              ∑ ν ∈ F.filter (fun ν => X.fj la v ν P x ≠ 0),
                Real.exp (-(3 * Real.pi / 2) * ∑ τ, ν τ) := by
            rw [Finset.mul_sum]
        _ ≤ max Cη 0 * Real.exp (-(Real.pi * c / X.firstMinimumSq x)) * Kf := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC10 (Real.exp_pos _).le)
            apply hKf
            intro ν hν
            rw [Finset.mem_filter] at hν
            unfold FrequencySumBounds.IsFreq
            refine ⟨hnn v hiso ν x hx hν.2, ?_⟩
            by_contra hcnd
            apply hν.2
            rw [Data.fj, if_neg hcnd]
    have hPx : ‖P x‖ * X.nfac la x ≤ max Cη 0 * Real.exp (-(Real.pi * c / X.firstMinimumSq x)) * Kf := by
      rcases hnf.eq_or_lt with h0 | hpos
      · rw [← h0, mul_zero]
        exact mul_nonneg (mul_nonneg hC10 (Real.exp_pos _).le) hK0
      · have hsumm : Summable (fun ν : X.Ψ → ℝ => ‖X.fj la v ν P x‖) := by
          refine summable_of_sum_le (c := max Cη 0 * Real.exp (-(Real.pi * c / X.firstMinimumSq x)) * Kf /
            X.nfac la x) (fun ν => norm_nonneg _) fun F => ?_
          rw [le_div_iff₀ hpos, Finset.sum_mul]
          exact hfin F
        have htle : ∑' ν, ‖X.fj la v ν P x‖ ≤
            max Cη 0 * Real.exp (-(Real.pi * c / X.firstMinimumSq x)) * Kf / X.nfac la x := by
          refine Real.tsum_le_of_sum_le (fun ν => norm_nonneg _) fun F => ?_
          rw [le_div_iff₀ hpos, Finset.sum_mul]
          exact hfin F
        rw [← le_div_iff₀ hpos, ← hsum.tsum_eq]
        exact (norm_tsum_le_tsum_norm hsumm).trans htle
    have hle : X.pnorm la P x ≤ max Cη 0 * Kf * Real.exp (-(Real.pi * c / X.firstMinimumSq x)) := by
      rw [hpn]
      linarith [hPx]
    have he2 : Real.exp (-(Real.pi * c / X.firstMinimumSq x)) ^ 2 =
        Real.exp (-2 * Real.pi * c / X.firstMinimumSq x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hP2 : X.pnorm la P x ^ 2 ≤ (max Cη 0 * Kf) ^ 2 * Real.exp (-2 * Real.pi * c / X.firstMinimumSq x) := by
      calc X.pnorm la P x ^ 2 ≤ (max Cη 0 * Kf * Real.exp (-(Real.pi * c / X.firstMinimumSq x))) ^ 2 :=
            pow_le_pow_left₀ hp0 hle 2
        _ = (max Cη 0 * Kf) ^ 2 * Real.exp (-2 * Real.pi * c / X.firstMinimumSq x) := by
            rw [mul_pow, he2]
    have hB2 : 0 ≤ B ^ 2 * Real.exp (2 * Real.pi * c / δ) * Real.exp (-2 * Real.pi * c / X.firstMinimumSq x) :=
      mul_nonneg (mul_nonneg (sq_nonneg B) (Real.exp_pos _).le) hexp.le
    nlinarith [hP2, hB2]
  · have hpB : X.pnorm la P x ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hp0 (hB x hx) 2
    have hcmp : 2 * Real.pi * c / X.firstMinimumSq x ≤ 2 * Real.pi * c / δ := by
      rcases le_or_gt (X.firstMinimumSq x) 0 with h | h
      · have hinv : (X.firstMinimumSq x)⁻¹ ≤ 0 := inv_nonpos.mpr h
        rw [div_eq_mul_inv]
        nlinarith [mul_nonneg h2pc (neg_nonneg.2 hinv), div_nonneg h2pc hδpos.le]
      · have hδL : δ ≤ X.firstMinimumSq x := by
          by_contra h'
          exact hL ⟨h, not_le.1 h'⟩
        rw [div_le_div_iff₀ h hδpos]
        exact mul_le_mul_of_nonneg_left hδL h2pc
    have hE : 1 ≤ Real.exp (2 * Real.pi * c / δ) * Real.exp (-2 * Real.pi * c / X.firstMinimumSq x) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have : -2 * Real.pi * c / X.firstMinimumSq x = -(2 * Real.pi * c / X.firstMinimumSq x) := by ring
      rw [this]
      linarith
    have hK2 : 0 ≤ (max Cη 0 * Kf) ^ 2 * Real.exp (-2 * Real.pi * c / X.firstMinimumSq x) :=
      mul_nonneg (sq_nonneg _) hexp.le
    calc X.pnorm la P x ^ 2 ≤ B ^ 2 := hpB
      _ ≤ B ^ 2 * (Real.exp (2 * Real.pi * c / δ) * Real.exp (-2 * Real.pi * c / X.firstMinimumSq x)) :=
          le_mul_of_one_le_right (sq_nonneg B) hE
      _ ≤ (B ^ 2 * Real.exp (2 * Real.pi * c / δ) + (max Cη 0 * Kf) ^ 2) *
            Real.exp (-2 * Real.pi * c / X.firstMinimumSq x) := by
          nlinarith [hK2]

end ReciprocityTheory.ChartRestriction.G.FD
