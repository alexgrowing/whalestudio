import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero

open NumberField IsDedekindDomain GlobalTheory.Mem Complex Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.Mem

theorem tsum_eq_exp_tsum_neg_log_of_primes {α ι : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    (p : ι → α) (hp : ∀ i, Prime (p i)) (hdvd : ∀ i j, p i ∣ p j → i = j)
    (f : α → ℂ) (hmul : ∀ a b, f (a * b) = f a * f b) (h1 : f 1 = 1)
    (hex : ∀ a, a ≠ 1 → f a ≠ 0 → ∃ i, p i ∣ a) (hsum : Summable fun a => ‖f a‖)
    (hne : ∀ i, 1 - f (p i) ≠ 0) :
    ∑' a, f a = exp (∑' i, -log (1 - f (p i))) := by
  classical
  set g : Finset ι → α → ℂ := fun S a => if ∀ i ∈ S, ¬ p i ∣ a then f a else 0 with hg
  have hgle : ∀ S a, ‖g S a‖ ≤ ‖f a‖ := by
    intro S a
    simp only [hg]
    split_ifs <;> simp
  have hgs : ∀ S, Summable (g S) := fun S => Summable.of_norm_bounded hsum (hgle S)
  have key : ∀ S : Finset ι, (∏ i ∈ S, (1 - f (p i))) * ∑' a, f a = ∑' a, g S a := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [hg]
    | insert i S hi ih =>
      rw [Finset.prod_insert hi, mul_assoc, ih]
      have hinj : Function.Injective fun b : α => p i * b := mul_right_injective₀ (hp i).ne_zero
      have e1 : ∀ a, g (insert i S) a = g S a - (if p i ∣ a then g S a else 0) := by
        intro a
        simp only [hg, Finset.forall_mem_insert]
        by_cases h : p i ∣ a <;> simp [h]
      have hs2 : Summable fun a => if p i ∣ a then g S a else 0 :=
        Summable.of_norm_bounded hsum (fun a => by
          split_ifs
          · exact hgle S a
          · simp)
      have e2 : ∑' a, (if p i ∣ a then g S a else 0) = f (p i) * ∑' a, g S a := by
        rw [← hinj.tsum_eq, ← tsum_mul_left]
        · refine tsum_congr fun b => ?_
          rw [if_pos (dvd_mul_right _ _)]
          have : (∀ j ∈ S, ¬ p j ∣ p i * b) ↔ ∀ j ∈ S, ¬ p j ∣ b := by
            refine forall₂_congr fun j hj => not_congr ?_
            rw [(hp j).dvd_mul]
            refine or_iff_right fun h => hi ?_
            rwa [← hdvd _ _ h]
          simp only [hg, this, hmul]
          split_ifs <;> simp
        · intro a ha
          by_cases h : p i ∣ a
          · obtain ⟨b, rfl⟩ := h
            exact ⟨b, rfl⟩
          · simp [h] at ha
      simp only [e1]
      rw [(hgs S).tsum_sub hs2, e2]
      ring
  have lim1 : Tendsto (fun S : Finset ι => ∑' a, g S a) atTop
      (𝓝 (∑' a : α, if a = 1 then (1 : ℂ) else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun a => ?_)
      (Eventually.of_forall fun S a => hgle S a)
    by_cases ha : a = 1
    · subst ha
      have : ∀ S, g S 1 = 1 := fun S => by
        simp only [hg]
        rw [if_pos fun i _ => (hp i).not_dvd_one, h1]
      simp [this]
    · rw [if_neg ha]
      by_cases hf : f a = 0
      · simp [hg, hf]
      · obtain ⟨i, hi⟩ := hex a ha hf
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with S hS
        simp only [hg]
        rw [if_neg]
        intro h
        exact h i (hS (Finset.mem_singleton_self i)) hi
  rw [tsum_ite_eq] at lim1
  have pinj : Function.Injective p := fun i j h => hdvd i j (h ▸ dvd_rfl)
  have hl : Summable fun i => log (1 - f (p i)) :=
    Summable.clog_one_sub (hsum.of_norm.comp_injective pinj)
  have lim2 : Tendsto (fun S : Finset ι => ∏ i ∈ S, (1 - f (p i))) atTop
      (𝓝 (exp (∑' i, log (1 - f (p i))))) := Complex.hasProd_of_hasSum_log hne hl.hasSum
  have lim3 := lim2.mul_const (∑' a, f a)
  simp only [key] at lim3
  have := tendsto_nhds_unique lim3 lim1
  rw [tsum_neg, exp_neg]
  exact eq_inv_of_mul_eq_one_right this

theorem lseriesSummable_card_absNorm (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1) ?_ (fun _ => Nat.cast_nonneg _)
    zero_le_one hs
  have h : Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  simp only [Real.rpow_one]
  exact Asymptotics.isBigO_of_div_tendsto_nhds (by
    filter_upwards [eventually_gt_atTop 0] with n hn h0
    exact absurd (Nat.cast_eq_zero.1 h0) hn.ne') _ h

instance finite_absNorm_fiber (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

theorem summable_norm_absNorm_cpow (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    Summable fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖ := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).summable_iff,
    summable_sigma_of_nonneg (fun _ => by exact norm_nonneg _)]
  refine ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card_absNorm K hs).norm.congr fun n => ?_
  have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ((fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖) ∘
        (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I))) ⟨n, I⟩ = ‖(n : ℂ) ^ (-s)‖ := by
    rintro ⟨I, rfl⟩; rfl
  rw [tsum_congr this, tsum_const]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hs0]
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← cpow_neg, norm_mul]
    simp

open Classical in

theorem RayData.coef_eq_tsum {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
    (χ : D.G →* ℂˣ) (n : ℕ) :
    D.coef χ n = ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      if IsCoprime I.1 (Ideal.span {(M : 𝓞 K)}) then (χ (D.cls I.1) : ℂ) else 0 := by
  have := Fintype.ofFinite {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  rw [tsum_fintype, RayData.coef, ← Finset.sum_filter,
    ← Finset.sum_fiberwise (g := fun I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n} => D.cls I.1)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => (χ c : ℂ)) (fun I hI => by
    rw [(Finset.mem_filter.1 hI).2]), Finset.sum_const, nsmul_eq_mul, mul_comm, RayData.cnt]
  congr 2
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun I => ⟨⟨I.1, I.2.2.1⟩, by simp [I.2.1, I.2.2.2]⟩
      invFun := fun I => ⟨I.1.1, by
        have := I.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact ⟨this.1, I.1.2, this.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem RayData.lseries_eq_exp_tsum :
    ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ) (s : ℂ), 1 < s.re → LSeriesSummable (D.coef χ) s ∧ Summable (fun v : D.Pr => ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖) ∧ LSeries (D.coef χ) s = Complex.exp (∑' v : D.Pr, -Complex.log (1 - (χ (D.cls v.1.asIdeal) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  classical
  intro K _ _ M _ D χ s hs
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hχ : ∀ c, ‖(χ c : ℂ)‖ = 1 := fun c => by
    refine (norm_eq_one_of_pow_eq_one (n := Fintype.card D.G) ?_ Fintype.card_ne_zero)
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  set f : Ideal (𝓞 K) → ℂ := fun I =>
    (if IsCoprime I (Ideal.span {(M : 𝓞 K)}) then (χ (D.cls I) : ℂ) else 0) *
      ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) with hf
  have hS := summable_norm_absNorm_cpow K hs
  have hsum : Summable fun I => ‖f I‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun I => ?_) hS
    simp only [hf, norm_mul]
    split_ifs <;> simp [hχ]
  have pinj : Function.Injective fun v : D.Pr => v.1.asIdeal := fun v w h =>
    Subtype.ext (HeightOneSpectrum.ext h)
  have hfp : ∀ v : D.Pr, f v.1.asIdeal =
      (χ (D.cls v.1.asIdeal) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) := fun v => by
    simp only [hf]
    rw [if_pos v.2]
  have hL : HasSum (LSeries.term (D.coef χ) s) (∑' I, f I) := by
    have h := hsum.of_norm.hasSum
    rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).hasSum_iff] at h
    refine h.sigma fun n => ?_
    have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
        (f ∘ (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I))) ⟨n, I⟩ =
          (if IsCoprime I.1 (Ideal.span {(M : 𝓞 K)}) then (χ (D.cls I.1) : ℂ) else 0) *
            (n : ℂ) ^ (-s) := by
      rintro ⟨I, rfl⟩; rfl
    simp only [this]
    have e : LSeries.term (D.coef χ) s n = D.coef χ n * (n : ℂ) ^ (-s) := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp [hs0]
      · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← cpow_neg]
    rw [e, RayData.coef_eq_tsum]
    exact (Summable.of_finite.hasSum).mul_right _
  refine ⟨hL.summable, hS.comp_injective pinj, ?_⟩
  rw [LSeries, hL.tsum_eq]
  simp only [← hfp]
  have hone : D.cls 1 = 1 := by
    have h := D.cls_mul 1 1 isCoprime_one_left isCoprime_one_left
    rw [mul_one] at h
    exact left_eq_mul.1 h
  refine tsum_eq_exp_tsum_neg_log_of_primes (fun v : D.Pr => v.1.asIdeal) (fun v => v.1.prime)
    (fun v w h => pinj ?_) f (fun I J => ?_) ?_ (fun I hI hfI => ?_) hsum (fun v => ?_)
  · exact (w.1.isMaximal.eq_of_le v.1.isPrime.ne_top (Ideal.le_of_dvd h)).symm
  · simp only [hf, IsCoprime.mul_left_iff, map_mul, Nat.cast_mul]
    rw [natCast_mul_natCast_cpow]
    by_cases hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})
    · by_cases hJ : IsCoprime J (Ideal.span {(M : 𝓞 K)})
      · simp only [hI, hJ, and_self, if_true, D.cls_mul I J hI hJ, map_mul, Units.val_mul]
        ring
      · simp [hJ]
    · simp [hI]
  · simp only [hf]
    rw [if_pos isCoprime_one_left, hone]
    simp
  · have hc : IsCoprime I (Ideal.span {(M : 𝓞 K)}) := by
      by_contra hc
      simp [hf, hc] at hfI
    have h0 : I ≠ ⊥ := by
      rintro rfl
      simp [hf, hs0] at hfI
    obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I (by simpa using hI)
    have hP0 : P ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hIP))
    have hd : P ∣ I := Ideal.dvd_iff_le.2 hIP
    exact ⟨⟨⟨P, hP.isPrime, hP0⟩, hc.of_isCoprime_of_dvd_left hd⟩, hd⟩
  · intro h
    have h1 : ‖f v.1.asIdeal‖ = 1 := by rw [← sub_eq_zero.1 h, norm_one]
    have hN : 1 < Ideal.absNorm v.1.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v.1
    rw [hfp, norm_mul, hχ, one_mul, norm_natCast_cpow_of_pos (by omega)] at h1
    refine absurd h1 (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN) ?_).ne
    simp only [neg_re]
    linarith

end GlobalTheory.Mem
