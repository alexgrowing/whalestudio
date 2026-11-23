import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegL1Norm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCoeffExpDecayOnCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumFourierSeriesOfExpDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnFourierCoeffFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCharacterBoundedAwayOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnSummableFourierSeriesStatement

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TauPeriod Complex
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.TauPeriod

theorem exists_tau_coboundary : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → ∀ a : Fin g → Pt E g → ℂ, (∀ k, DifferentiableOn ℂ (a k) (cov U g)) → (∀ k j, ∀ P ∈ cov U g, a k (P.1, P.2 + Pi.single j 1) = a k P) → (∀ k j, ∀ P ∈ cov U g, a k (transl τ (Pi.single (Sum.inl j) 1) P) + a j P = a j (transl τ (Pi.single (Sum.inl k) 1) P) + a k P) → ∀ b₀ ∈ U, ∃ r > 0, Metric.ball b₀ r ⊆ U ∧ ∃ (ψ : Pt E g → ℂ) (s : Fin g → E → ℂ), DifferentiableOn ℂ ψ (cov (Metric.ball b₀ r) g) ∧ (∀ j, ∀ P ∈ cov (Metric.ball b₀ r) g, ψ (P.1, P.2 + Pi.single j 1) = ψ P) ∧ (∀ k, ContinuousOn (s k) (Metric.ball b₀ r)) ∧ ∀ k, ∀ P ∈ cov (Metric.ball b₀ r) g, ψ (transl τ (Pi.single (Sum.inl k) 1) P) = ψ P + a k P - s k P.1 := by
  intro E _ _ _ g U τ hτ a hdiff hper hcoc b₀ hb₀
  classical
  have hUo : IsOpen U := hτ.1
  have hcovo : IsOpen (cov U g) := hUo.prod isOpen_univ
  obtain ⟨r, hr, hsub, δ, hδ, hk⟩ := GlobalTheory.T.period_character_bounded_away_one hτ b₀ hb₀
  choose kk hkk using hk
  set V := Metric.ball b₀ r with hV
  have hVU : V ⊆ U := Metric.ball_subset_closedBall.trans hsub
  have hVo : IsOpen V := Metric.isOpen_ball

  have hfb : ∀ k, ∀ b ∈ U, Differentiable ℂ (fun z => a k (b, z)) := by
    intro k b hb z
    have h1 : DifferentiableAt ℂ (a k) (b, z) :=
      (hdiff k).differentiableAt (hcovo.mem_nhds ⟨hb, Set.mem_univ _⟩)
    exact h1.comp z ((differentiableAt_const b).prodMk differentiableAt_id)
  have hpb : ∀ k, ∀ b ∈ U, ∀ (j : Fin g) z, a k (b, z + Pi.single j 1) = a k (b, z) :=
    fun k b hb j z => hper k j (b, z) ⟨hb, Set.mem_univ _⟩
  set c : Fin g → (Fin g → ℤ) → E → ℂ := fun k n b => cf (fun z => a k (b, z)) n with hc
  set T : E → Fin g → Fin g → ℂ := fun b k => per (τ b) (Pi.single (Sum.inl k) 1) with hT
  have hTe : ∀ b k, T b k = fun i => τ b k i := by
    intro b k
    funext i
    simp [hT, per, vecMul, dotProduct, Pi.single_apply]
    simp only [apply_ite (fun t : ℝ => (t : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

  have cf_add : ∀ (f h : (Fin g → ℂ) → ℂ), Continuous f → Continuous h → ∀ n,
      cf (fun z => f z + h z) n = cf f n + cf h n := by
    intro f h hf hh n
    unfold cf
    rw [← integral_add]
    · congr 1
      funext x
      ring
    · exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc
    · exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc

  have hid : ∀ b ∈ U, ∀ n k j, c k n b * ex n (T b j) + c j n b = c j n b * ex n (T b k) + c k n b := by
    intro b hb n k j
    have e1 : cf (fun z => a k (b, z + T b j) + a j (b, z)) n
        = cf (fun z => a j (b, z + T b k) + a k (b, z)) n := by
      congr 1
      funext z
      exact hcoc k j (b, z) ⟨hb, Set.mem_univ _⟩
    have hc1 := (hfb k b hb).continuous
    have hc2 := (hfb j b hb).continuous
    have e2 := cf_add (fun z => a k (b, z + T b j)) (fun z => a j (b, z))
      (show Continuous fun z => a k (b, z + T b j) from hc1.comp (continuous_add_right _)) hc2 n
    have e3 := cf_add (fun z => a j (b, z + T b k)) (fun z => a k (b, z))
      (show Continuous fun z => a j (b, z + T b k) from hc2.comp (continuous_add_right _)) hc1 n
    have e4 : cf (fun z => a k (b, z + T b j)) n = ex n (T b j) * cf (fun z => a k (b, z)) n :=
      cf_translate _ (hfb k b hb) (hpb k b hb) n _
    have e5 : cf (fun z => a j (b, z + T b k)) n = ex n (T b k) * cf (fun z => a j (b, z)) n :=
      cf_translate _ (hfb j b hb) (hpb j b hb) n _
    rw [e2, e3, e4, e5] at e1
    simp only [hc]
    linear_combination e1

  set d : (Fin g → ℤ) → E → ℂ := fun n b =>
    if h : n = 0 then 0 else c (kk n h) n b / (ex n (T b (kk n h)) - 1) with hd
  have hden : ∀ n (h : n ≠ 0), ∀ b ∈ Metric.closedBall b₀ r, ex n (T b (kk n h)) - 1 ≠ 0 := by
    intro n h b hb h0
    have := hkk n h b hb
    have h0' : ex n (per (τ b) (Pi.single (Sum.inl (kk n h)) 1)) - 1 = 0 := h0
    rw [h0', norm_zero] at this
    linarith
  have hdk : ∀ n, n ≠ 0 → ∀ k, ∀ b ∈ Metric.closedBall b₀ r,
      d n b * (ex n (T b k) - 1) = c k n b := by
    intro n h k b hb
    have hD := hden n h b hb
    have e := hid b (hsub hb) n k (kk n h)
    simp only [hd, dif_neg h]
    rw [div_mul_eq_mul_div, div_eq_iff hD]
    linear_combination -e
  have hexT : ∀ n k, DifferentiableOn ℂ (fun b => ex n (T b k)) U := by
    intro n k
    have : ∀ i, DifferentiableOn ℂ (fun b => τ b k i) U := fun i => hτ.2.1 k i
    simp only [hTe, ex]
    exact (DifferentiableOn.cexp (DifferentiableOn.const_mul
      (DifferentiableOn.fun_sum fun i _ => (this i).const_mul _) _))
  have hdd : ∀ n, DifferentiableOn ℂ (d n) V := by
    intro n
    by_cases h : n = 0
    · simp only [hd, dif_pos h]
      exact differentiableOn_const _
    · simp only [hd, dif_neg h, div_eq_mul_inv]
      intro b hb
      have hb' := hden n h b (Metric.ball_subset_closedBall hb)
      have h1 := ((GlobalTheory.T.differentiableOn_fourier_coeff_family (a (kk n h)) hUo (hdiff _) n) b (hVU hb)).mono hVU
      have h2 := (((hexT n (kk n h)) b (hVU hb)).fun_sub (differentiableWithinAt_const 1)).mono hVU
      exact h1.fun_mul (h2.fun_inv hb')
  have hdecay : ∀ K ⊆ V, IsCompact K → ∀ R : ℝ, 0 ≤ R → ∃ M : ℝ, ∀ n, ∀ b ∈ K,
      ‖d n b‖ ≤ M * Real.exp (-(2 * π * R) * l1 n) := by
    intro K hK hKc R hR
    choose M hM using fun k => GlobalTheory.T.fourier_coeff_exp_decay_on_compact (a k) hUo (hdiff k) (hper k) K (hK.trans hVU) hKc R hR
    refine ⟨(∑ k, |M k|) / δ, fun n b hb => ?_⟩
    have hE := Real.exp_pos (-(2 * π * R) * l1 n)
    have hS : 0 ≤ ∑ k, |M k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    by_cases h : n = 0
    · simp only [hd, dif_pos h, norm_zero]
      positivity
    · simp only [hd, dif_neg h]
      have hbb : b ∈ Metric.closedBall b₀ r := Metric.ball_subset_closedBall (hK hb)
      have h1 := hkk n h b hbb
      have h2 := hM (kk n h) n b hb
      have h3 : M (kk n h) ≤ ∑ k, |M k| :=
        (le_abs_self _).trans (Finset.single_le_sum (f := fun k => |M k|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ _))
      rw [norm_div, div_le_iff₀ (hδ.trans_le h1)]
      calc ‖c (kk n h) n b‖ ≤ M (kk n h) * Real.exp (-(2 * π * R) * l1 n) := h2
        _ ≤ (∑ k, |M k|) * Real.exp (-(2 * π * R) * l1 n) := by gcongr
        _ = (∑ k, |M k|) / δ * Real.exp (-(2 * π * R) * l1 n) * δ := by
          field_simp
        _ ≤ (∑ k, |M k|) / δ * Real.exp (-(2 * π * R) * l1 n) *
            ‖ex n (per (τ b) (Pi.single (Sum.inl (kk n h)) 1)) - 1‖ := by gcongr
  obtain ⟨hψd, hψs⟩ := GlobalTheory.T.differentiableOn_summable_fourier_series d hVo hdd hdecay
  refine ⟨r, hr, hVU, fun P => ∑' n, d n P.1 * ex n P.2, fun k b => c k 0 b, hψd, ?_, ?_, ?_⟩
  · intro j P _
    simp only [ex_add_single]
  · intro k
    exact ((GlobalTheory.T.differentiableOn_fourier_coeff_family (a k) hUo (hdiff k) 0).continuousOn).mono hVU
  · intro k P hP
    obtain ⟨b, z⟩ := P
    have hb : b ∈ V := hP.1
    have hbU : b ∈ U := hVU hb
    have hbc : b ∈ Metric.closedBall b₀ r := Metric.ball_subset_closedBall hb
    have hA : HasSum (fun n => d n b * ex n z) (∑' n, d n b * ex n z) :=
      (hψs (b, z) hb).hasSum
    have hB : HasSum (fun n => c k n b * ex n z) (a k (b, z)) := by
      refine GlobalTheory.T.hasSum_fourier_series_of_exp_decay (fun z => a k (b, z)) (hfb k b hbU) (hpb k b hbU) (fun R hR => ?_) z
      obtain ⟨M, hM⟩ := GlobalTheory.T.fourier_coeff_exp_decay_on_compact (a k) hUo (hdiff k) (hper k) {b}
        (Set.singleton_subset_iff.2 hbU) isCompact_singleton R hR
      exact ⟨M, fun n => hM n b rfl⟩
    have hC := (hA.add hB).sub (hasSum_ite_eq (0 : Fin g → ℤ) (c k 0 b))
    show ∑' n, d n b * ex n (z + per (τ b) (Pi.single (Sum.inl k) 1)) = _
    rw [← hC.tsum_eq]
    refine tsum_congr fun n => ?_
    by_cases h : n = 0
    · subst h
      simp [hd, ex_zero]
    · have := hdk n h k b hbc
      rw [if_neg h, ex_add]
      simp only [hT] at this
      linear_combination (ex n z) * this

end GlobalTheory.TauPeriod
