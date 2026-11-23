import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementC
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)

namespace TraceNormBounds

theorem poly_id (l : ℕ) (hl : l.Prime) : ∃ Q : Polynomial ℤ,
    (Polynomial.X ^ l - Polynomial.X - ∏ n ∈ Finset.range l,
      (Polynomial.X - ((n : ℕ) : Polynomial ℤ)) : Polynomial ℤ) = Polynomial.C (l : ℤ) * Q := by
  have : Fact l.Prime := ⟨hl⟩
  have : NeZero l := ⟨hl.ne_zero⟩
  have hprod : ∏ a : ZMod l, (Polynomial.X - Polynomial.C a) =
      (Polynomial.X ^ l - Polynomial.X : Polynomial (ZMod l)) := by
    have hr := FiniteField.roots_X_pow_card_sub_X (ZMod l)
    rw [ZMod.card] at hr
    have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod l) hl.one_lt
    have hmon : (Polynomial.X ^ l - Polynomial.X : Polynomial (ZMod l)).Monic := by
      apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X]
      exact_mod_cast hl.one_lt
    have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
      (by rw [hr, hdeg]; simp)
    rw [hr] at h
    exact h
  have hrange : ∏ n ∈ Finset.range l, (Polynomial.X - ((n : ℕ) : Polynomial (ZMod l))) =
      ∏ a : ZMod l, (Polynomial.X - Polynomial.C a) := by
    refine Finset.prod_bij (fun n _ => ((n : ℕ) : ZMod l)) (fun _ _ => Finset.mem_univ _) ?_ ?_
      (fun _ _ => by rw [map_natCast])
    · intro a ha b hb hab
      have := congrArg ZMod.val hab
      rwa [ZMod.val_natCast_of_lt (Finset.mem_range.1 ha),
        ZMod.val_natCast_of_lt (Finset.mem_range.1 hb)] at this
    · intro b _
      exact ⟨b.val, Finset.mem_range.2 (ZMod.val_lt b), by simp⟩
  change Polynomial.C (l : ℤ) ∣ _
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hmap : Polynomial.map (Int.castRingHom (ZMod l))
      (Polynomial.X ^ l - Polynomial.X - ∏ n ∈ Finset.range l,
        (Polynomial.X - ((n : ℕ) : Polynomial ℤ)) : Polynomial ℤ) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_natCast]
    rw [hrange, hprod, sub_self]
  have h := congrArg (fun P => Polynomial.coeff P i) hmap
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at h
  exact h

section Normed

variable {K : Type} [NormedField K] [IsUltrametricDist K]

private lemma norm_finset_sum_le_one_of_norm_le_one {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∑ i ∈ s, f i‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

private lemma norm_natCast_le_one_kummer_theta_logarithms (n : ℕ) : ‖(n : K)‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))

private lemma int_lemma_3 (z : ℤ) : ‖(z : K)‖ ≤ 1 := by
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · exact_mod_cast norm_natCast_le_one_kummer_theta_logarithms n
  · rw [Int.cast_neg, norm_neg]
    exact_mod_cast norm_natCast_le_one_kummer_theta_logarithms n

theorem norm_eval_le (Q : Polynomial ℤ) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖Polynomial.eval₂ (Int.castRingHom K) x Q‖ ≤ 1 := by
  rw [Polynomial.eval₂_eq_sum_range]
  apply norm_finset_sum_le_one_of_norm_le_one
  intro i _
  have hc : ‖(Int.castRingHom K) (Q.coeff i)‖ ≤ 1 := by
    rw [eq_intCast]
    exact int_lemma_3 _
  have hp : ‖x ^ i‖ ≤ 1 := by
    rw [norm_pow]
    first
    | exact pow_le_one₀ (norm_nonneg _) hx
    | exact pow_le_one _ (norm_nonneg _) hx
  rw [norm_mul]
  first
  | exact mul_le_one₀ hc (norm_nonneg _) hp
  | exact mul_le_one' hc hp
  | nlinarith [norm_nonneg ((Int.castRingHom K) (Q.coeff i)), norm_nonneg (x ^ i)]

theorem norm_le_inv_of_lt_one {l : ℕ} (hl : 1 < l)
    (hval : ∀ a : K, a ≠ 0 → ∃ k : ℤ, ‖a‖ = (l : ℝ) ^ k) {y : K} (hy : ‖y‖ < 1) :
    ‖y‖ ≤ (l : ℝ)⁻¹ := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  obtain ⟨k, hk⟩ := hval y hy0
  rw [hk] at hy ⊢
  have hl' : (1 : ℝ) < l := by exact_mod_cast hl
  have hk' : k < 0 := by
    by_contra hc
    push_neg at hc
    have h1 : (1 : ℝ) ≤ (l : ℝ) ^ k := by
      first
      | exact one_le_zpow₀ hl'.le hc
      | exact one_le_zpow_of_nonneg₀ hl'.le hc
    linarith
  have h2 : (l : ℝ) ^ k ≤ (l : ℝ) ^ (-1 : ℤ) := by
    first
    | exact zpow_le_zpow_right₀ hl'.le (by omega)
    | exact zpow_le_of_le hl'.le (by omega)
  simpa using h2

end Normed

end TraceNormBounds

open TraceNormBounds

theorem sigma_isometry : SigmaIsom := by
  unfold SigmaIsom
  intro K _ _ _ l σ hU a
  obtain ⟨hp, h2, hnp, hval, hfr⟩ := hU
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hl : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hl0 : (l : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have unit : ∀ u : K, ‖u‖ = 1 → ‖σ u‖ = 1 := by
    intro u hu
    have h1 := hfr u hu.le
    have h3 : ‖u ^ l‖ = 1 := by rw [norm_pow, hu, one_pow]
    have h4 : ‖σ u - u ^ l‖ < ‖u ^ l‖ := by
      rw [h3]
      exact lt_of_le_of_lt h1 (inv_lt_one_of_one_lt₀ hl)
    have e : σ u = (σ u - u ^ l) + u ^ l := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h4.ne, h3]
    exact max_eq_right (h4.trans_eq h3).le
  obtain ⟨k, hk⟩ := hval a ha
  have hnu : ‖a * (l : K) ^ k‖ = 1 := by
    rw [norm_mul, norm_zpow, hnp, hk, inv_zpow, mul_inv_cancel₀ (zpow_ne_zero k (by positivity))]
  have ha' : a = (a * (l : K) ^ k) * (l : K) ^ (-k) := by
    rw [mul_assoc, ← zpow_add₀ hl0, add_neg_cancel, zpow_zero, mul_one]
  rw [ha', map_mul, map_zpow₀, map_natCast, norm_mul, norm_mul, unit _ hnu, hnu]

theorem fixed_is_limit : FixedIsLimit := by
  intro K _ _ _ l σ hU
  obtain ⟨hp, hp2, hpn, hval, hσ⟩ := hU
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  have hinv : ((l : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hlK : (l : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have step : ∀ x : K, ‖x‖ ≤ 1 → σ x = x → ∃ n : ℕ, ‖x - n‖ ≤ (l : ℝ)⁻¹ := by
    intro x hx hfix
    obtain ⟨Q, hQ⟩ := poly_id l hp
    have hev := congrArg (Polynomial.eval₂ (Int.castRingHom K) x) hQ
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_finsetProd] at hev
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_natCast, eq_intCast,
      Int.cast_natCast] at hev
    have h1 : ‖x ^ l - x‖ ≤ (l : ℝ)⁻¹ := by
      have := hσ x hx
      rwa [hfix, norm_sub_rev] at this
    have h2 : ‖(l : K) * Polynomial.eval₂ (Int.castRingHom K) x Q‖ ≤ (l : ℝ)⁻¹ := by
      rw [norm_mul, hpn]
      exact mul_le_of_le_one_right (by positivity) (norm_eval_le Q hx)
    have h3 : ‖∏ n ∈ Finset.range l, (x - (n : K))‖ ≤ (l : ℝ)⁻¹ := by
      have e : ∏ n ∈ Finset.range l, (x - (n : K)) =
          (x ^ l - x) - (l : K) * Polynomial.eval₂ (Int.castRingHom K) x Q := by
        rw [← hev]; ring
      rw [e, sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by rwa [norm_neg]))
    by_contra hc
    push Not at hc
    have h4 : ∀ n ∈ Finset.range l, (1 : ℝ) ≤ ‖x - (n : K)‖ := by
      intro n _
      by_contra hlt
      exact absurd (norm_le_inv_of_lt_one hp.one_lt hval (not_le.1 hlt)) (not_le.2 (hc n))
    have h5 : (1 : ℝ) ≤ ‖∏ n ∈ Finset.range l, (x - (n : K))‖ := by
      rw [norm_prod]
      have := Finset.prod_le_prod (s := Finset.range l) (f := fun _ => (1 : ℝ))
        (g := fun n : ℕ => ‖x - (n : K)‖) (fun _ _ => zero_le_one) h4
      simpa using this
    linarith
  intro x hx hfix k
  induction k generalizing x with
  | zero => exact ⟨0, by simpa using hx⟩
  | succ k ih =>
    obtain ⟨n0, hn0⟩ := step x hx hfix
    have hy : ‖(x - n0) / (l : K)‖ ≤ 1 := by
      rw [norm_div, hpn, div_inv_eq_mul]
      calc ‖x - n0‖ * l ≤ (l : ℝ)⁻¹ * l := by gcongr
        _ = 1 := inv_mul_cancel₀ hl0
    have hyf : σ ((x - n0) / (l : K)) = (x - n0) / (l : K) := by
      rw [map_div₀, map_sub, map_natCast, map_natCast, hfix]
    obtain ⟨m, hm⟩ := ih _ hy hyf
    refine ⟨n0 + l * m, ?_⟩
    have e : x - ((n0 + l * m : ℕ) : K) = (l : K) * ((x - n0) / (l : K) - m) := by
      push_cast
      field_simp
      ring
    rw [e, norm_mul, hpn, pow_succ, mul_inv, mul_comm]
    gcongr

theorem simeq_fixed : SimeqFixed := by
  intro K _ _ _ l σ hU τ _ f c hc hfix hs
  obtain ⟨hp, hp2, hpn, hval, hσ⟩ := hU
  obtain ⟨h0, hI⟩ := hs
  rw [sub_zero] at h0 hI
  have hp0 : l ≠ 0 := hp.ne_zero
  have hD := Formalism.InvariantFactorPaths.G7.Top.dworkMv
  have h0' : MvPowerSeries.constantCoeff (MvPowerSeries.C c * f) = 0 := by simp [h0]
  refine ⟨by rwa [sub_zero], ?_⟩
  rw [sub_zero, hD K τ l σ hp hpn hσ _ h0']
  have hcf := (hD K τ l σ hp hpn hσ f h0).1 hI
  intro n
  have he : frobVar l (MvPowerSeries.map σ (MvPowerSeries.C c * f)) -
      MvPowerSeries.C (l : K) * (MvPowerSeries.C c * f) =
      MvPowerSeries.C c * (frobVar l (MvPowerSeries.map σ f) - MvPowerSeries.C (l : K) * f) := by
    rw [map_mul, MvPowerSeries.map_C, hfix, Formalism.InvariantFactorPaths.G7.frobVar_eq_expand hp0,
      Formalism.InvariantFactorPaths.G7.frobVar_eq_expand hp0, map_mul, MvPowerSeries.expand_C]
    ring
  rw [he, MvPowerSeries.coeff_C_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hcf n)

theorem simeq_closed : SimeqClosed := by
  intro K _ _ _ l σ hU τ _ f g hlim hf
  have hiso := sigma_isometry K l σ hU
  obtain ⟨hp, hp2, hpn, hval, hσ⟩ := hU
  have hp0 : l ≠ 0 := hp.ne_zero
  have hD := Formalism.InvariantFactorPaths.G7.Top.dworkMv
  have hcont : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ hiso).continuous
  have hf0 : ∀ k, MvPowerSeries.constantCoeff (f k) = 0 := fun k => by
    have := (hf k).1
    rwa [sub_zero] at this
  have hg0 : MvPowerSeries.constantCoeff g = 0 := by
    have h := hlim 0
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf0] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  refine ⟨by rwa [sub_zero], ?_⟩
  rw [sub_zero, hD K τ l σ hp hpn hσ _ hg0]
  intro n
  have hk : ∀ k, ‖MvPowerSeries.coeff n (frobVar l (MvPowerSeries.map σ (f k)) -
      MvPowerSeries.C (l : K) * f k)‖ ≤ (l : ℝ)⁻¹ := fun k =>
    (hD K τ l σ hp hpn hσ _ (hf0 k)).1 (by have := (hf k).2; rwa [sub_zero] at this) n
  have hT : Filter.Tendsto (fun k => MvPowerSeries.coeff n (frobVar l (MvPowerSeries.map σ (f k)) -
      MvPowerSeries.C (l : K) * f k)) Filter.atTop
      (nhds (MvPowerSeries.coeff n (frobVar l (MvPowerSeries.map σ g) -
        MvPowerSeries.C (l : K) * g))) := by
    simp only [map_sub, MvPowerSeries.coeff_C_mul]
    refine Filter.Tendsto.sub ?_ ((hlim n).const_mul _)
    by_cases hd : ∀ i, l ∣ n i
    · obtain ⟨m, rfl⟩ : ∃ m : τ →₀ ℕ, n = l • m := by
        refine ⟨n.mapRange (· / l) (by simp), ?_⟩
        ext i
        simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
        exact (Nat.mul_div_cancel' (hd i)).symm
      simp only [Formalism.InvariantFactorPaths.G7.coeff_frobVar_smul hp0, MvPowerSeries.coeff_map]
      exact (hcont.tendsto _).comp (hlim m)
    · push Not at hd
      obtain ⟨i, hi⟩ := hd
      simp only [Formalism.InvariantFactorPaths.G7.coeff_frobVar_of_not_dvd hp0 _ hi]
      exact tendsto_const_nhds
  exact le_of_tendsto hT.norm (Filter.Eventually.of_forall hk)

end Formalism.L2.Th1.D
