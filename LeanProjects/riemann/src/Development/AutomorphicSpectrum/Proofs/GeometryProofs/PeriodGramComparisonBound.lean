import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogBoundEventuallyBounds

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

theorem logBound_term_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : 0 ≤ Real.log (1 / x ^ 2) := by
  rcases h0.eq_or_lt with h | h
  · subst h
    simp
  · apply Real.log_nonneg
    rw [le_div_iff₀ (pow_pos h 2), _root_.one_mul]
    nlinarith

theorem uncentre_recentre {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) :
    uncentre t₀ ρ π (recentre t₀ ρ π u) = u := by
  funext i
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  simp only [uncentre, recentre, Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
    Equiv.apply_symm_apply, add_sub_cancel_left]
  rw [← _root_.mul_assoc, inv_mul_cancel₀ hρ', _root_.one_mul]

theorem lipschitz_uncentre {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) :
    LipschitzWith (Real.toNNReal ρ⁻¹) (uncentre t₀ ρ π) := by
  refine LipschitzWith.of_dist_le_mul fun t s => ?_
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr hρ.le)]
  refine (dist_pi_le_iff (mul_nonneg (inv_nonneg.mpr hρ.le) dist_nonneg)).2 fun i => ?_
  simp only [uncentre, dist_eq_norm]
  rw [← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le,
    sub_sub_sub_cancel_right]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (t - s) (π.symm i)) (inv_nonneg.mpr hρ.le)

theorem norm_fderiv_comp_uncentre {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : (Fin n → ℂ) → E) (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    ‖fderiv ℝ (fun t' => G (uncentre t₀ ρ π t')) t‖ ≤ ‖fderiv ℝ G (uncentre t₀ ρ π t)‖ * ρ⁻¹ := by
  have hdu : Differentiable ℝ (uncentre t₀ ρ π) := by
    unfold uncentre
    fun_prop
  by_cases hG : DifferentiableAt ℝ G (uncentre t₀ ρ π t)
  · rw [show (fun t' => G (uncentre t₀ ρ π t')) = G ∘ uncentre t₀ ρ π from rfl, fderiv_comp t hG (hdu t)]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := t) (lipschitz_uncentre t₀ hρ π)
    rwa [Real.coe_toNNReal _ (inv_nonneg.mpr hρ.le)] at h
  · have hnd : ¬ DifferentiableAt ℝ (fun t' => G (uncentre t₀ ρ π t')) t := by
      intro h
      apply hG
      have hdr : Differentiable ℝ (recentre t₀ ρ π) := by
        unfold recentre
        fun_prop
      have h' : DifferentiableAt ℝ (fun t' => G (uncentre t₀ ρ π t'))
          (recentre t₀ ρ π (uncentre t₀ ρ π t)) := by
        rw [recentre_uncentre t₀ hρ π t]
        exact h
      have h2 := h'.comp (uncentre t₀ ρ π t) (hdr _)
      have he : ((fun t' => G (uncentre t₀ ρ π t')) ∘ recentre t₀ ρ π) = G := by
        funext u
        simp only [Function.comp_apply, uncentre_recentre t₀ hρ π u]
      rwa [he] at h2
    rw [fderiv_zero_of_not_differentiableAt hnd, norm_zero]
    exact mul_nonneg (norm_nonneg _) (inv_nonneg.mpr hρ.le)

theorem logBound_weight_le {n a₀ a : ℕ} {t₀ t : Fin n → ℂ} {π : Equiv.Perm (Fin n)} {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hπ : ∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < a ∧ t₀ (π.symm i) = 0) (ht : ‖t‖ < 1)
    (hu : ∀ i : Fin n, (i : ℕ) < a₀ → uncentre t₀ ρ π t i ≠ 0) :
    (∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) ≤
      ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0 := by
  have hf : ∀ j : Fin n, 0 ≤ Real.log (1 / ‖t j‖ ^ 2) := fun j =>
    logBound_term_nonneg (norm_nonneg _) (lt_of_le_of_lt (norm_le_pi_norm t j) ht)
  calc (∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0)
      ≤ ∑ i : Fin n, if ((π.symm i : Fin n) : ℕ) < a then Real.log (1 / ‖t (π.symm i)‖ ^ 2) else 0 := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with h1 h2 h2
        · have hj := hπ i h1
          have hne := hu i h1
          have hx : ‖uncentre t₀ ρ π t i‖ = ρ⁻¹ * ‖t (π.symm i)‖ := by
            simp only [uncentre, hj.2, sub_zero, norm_mul, norm_inv, Complex.norm_real,
              Real.norm_of_nonneg hρ.le]
          have htpos : 0 < ‖t (π.symm i)‖ := by
            refine lt_of_le_of_ne (norm_nonneg _) (Ne.symm ?_)
            intro h0
            apply hne
            rw [← norm_eq_zero, hx, h0, mul_zero]
          have hρi : 1 ≤ ρ⁻¹ := (one_le_inv₀ hρ).mpr hρ1
          rw [hx]
          apply Real.log_le_log (one_div_pos.mpr (pow_pos (mul_pos (inv_pos.mpr hρ) htpos) 2))
          apply one_div_le_one_div_of_le (pow_pos htpos 2)
          exact pow_le_pow_left₀ (norm_nonneg _) (le_mul_of_one_le_left (norm_nonneg _) hρi) 2
        · exact absurd (hπ i h1).1 h2
        · exact hf _
        · exact le_rfl
    _ = ∑ j : Fin n, if (j : ℕ) < a then Real.log (1 / ‖t j‖ ^ 2) else 0 :=
        Equiv.sum_comp π.symm (fun j => if (j : ℕ) < a then Real.log (1 / ‖t j‖ ^ 2) else 0)

theorem logBound_recentred : ∀ (n a₀ g r a : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ) (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ) (π : Equiv.Perm (Fin n)) (ρ : ℝ), 0 < ρ → ρ ≤ 1 → (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) → LinearIndependent ℂ (fun k => U k 0) → (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < a ∧ t₀ (π.symm i) = 0) → ∃ ε c C : ℝ, 0 < ε ∧ ε ≤ ρ ∧ 0 < c ∧ 0 < C ∧ ∀ t : Fin n → ℂ, ‖t - t₀‖ < ε → ‖t‖ < 1 → HodgeMetric.uncentre t₀ ρ π t ∈ Flat.punct n a₀ 1 → ((HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹ - (c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).PosSemidef ∧ (((C * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - (HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹).PosSemidef ∧ ∀ p q, ‖fderiv ℝ (fun t' => HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t') p q) t‖ ≤ C * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) / 2) := by
  intro n a₀ g r a Λ _ L U t₀ π ρ hρ hρ1 hU hli hπ
  obtain ⟨ρ', c, C', hρ', hc, hC', hb⟩ :=
    GlobalTheory.CompanionTheory.Ar.Cusp.logBound_subframe n a₀ g r Λ L U (periodGram L U) hU hli (fun z i j => rfl)
  refine ⟨min ρ (ρ * ρ'), c, C' / ρ, lt_min hρ (mul_pos hρ hρ'), min_le_left _ _, hc, div_pos hC' hρ, ?_⟩
  intro t htε ht hpun
  have hzb : uncentre t₀ ρ π t ∈ Flat.punct n a₀ ρ' := by
    refine ⟨?_, hpun.2⟩
    have h1 := (lipschitz_uncentre t₀ hρ π).dist_le_mul t t₀
    rw [uncentre_self, Real.coe_toNNReal _ (inv_nonneg.mpr hρ.le), dist_eq_norm t t₀] at h1
    have h2 : ‖t - t₀‖ < ρ * ρ' := lt_of_lt_of_le htε (min_le_right _ _)
    rw [Metric.mem_ball]
    calc dist (uncentre t₀ ρ π t) 0 ≤ ρ⁻¹ * ‖t - t₀‖ := h1
      _ < ρ⁻¹ * (ρ * ρ') := mul_lt_mul_of_pos_left h2 (inv_pos.mpr hρ)
      _ = ρ' := by rw [← _root_.mul_assoc, inv_mul_cancel₀ hρ.ne', _root_.one_mul]
  obtain ⟨b1, b2, b3⟩ := hb _ hzb
  have hle := logBound_weight_le hρ hρ1 hπ ht hpun.2
  have hX'0 : 0 ≤ (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) := by
    refine add_nonneg (Real.exp_pos 1).le (Finset.sum_nonneg fun i _ => ?_)
    split_ifs
    · exact logBound_term_nonneg (norm_nonneg _) (lt_of_le_of_lt (norm_le_pi_norm t i) ht)
    · exact le_rfl
  have hS : (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) ≤ (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) := by linarith
  have hCρ : C' ≤ C' / ρ := le_div_self hC'.le hρ hρ1
  have hCC : C' * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) ≤ C' / ρ * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) :=
    (mul_le_mul_of_nonneg_left hS hC'.le).trans (mul_le_mul_of_nonneg_right hCρ hX'0)
  refine ⟨b1, ?_, ?_⟩
  · have hd : 0 ≤ C' / ρ * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) - C' * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) := by linarith
    have hsplit : (((C' / ρ * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) : ℝ)) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - (HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹ =
        ((((C' * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) : ℝ)) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - (HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹) +
          (((C' / ρ * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) - C' * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) : ℝ)) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
      rw [Complex.ofReal_sub, sub_smul]
      abel
    rw [hsplit]
    exact b2.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hd))
  · intro p q
    calc ‖fderiv ℝ (fun t' => HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t') p q) t‖
        ≤ ‖fderiv ℝ (fun w => periodGram L U w p q) (uncentre t₀ ρ π t)‖ * ρ⁻¹ :=
          norm_fderiv_comp_uncentre (fun w => periodGram L U w p q) t₀ hρ π t
      _ ≤ C' * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) / 2) * ρ⁻¹ :=
          mul_le_mul_of_nonneg_right (b3 p q) (inv_nonneg.mpr hρ.le)
      _ = C' * ρ⁻¹ * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) / 2) := by ring
      _ ≤ C' * ρ⁻¹ * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) / 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
            (mul_nonneg hC'.le (inv_nonneg.mpr hρ.le))
      _ = C' / ρ * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) / 2) := by ring

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
