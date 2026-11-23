import Mathlib

noncomputable section

namespace ReciprocityTheory.Neutral.Bridge

open NumberField IsDedekindDomain Filter Topology

variable (K : Type*) [Field K] [NumberField K]

namespace DedekindZetaReal

def zetaReal (s : ℝ) : ℝ :=
  ∑' n : ℕ, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)

theorem zetaReal_tendsto_sum_card_div : ∃ c : ℝ, Tendsto (fun n : ℕ ↦
    (∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / n)
      atTop (𝓝 c) := by
  refine ⟨_, ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
    fun n ↦ ?_⟩
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem zetaReal_term_eq {s : ℝ} (hs : 0 < s) (n : ℕ) :
    LSeries.term (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) (s : ℂ) n =
      (((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
  · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_neg, Complex.cpow_neg, div_eq_mul_inv]
    simp

theorem summable_zetaReal {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ =>
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) := by
  obtain ⟨c, hc⟩ := zetaReal_tendsto_sum_card_div K
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ))
      =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    simp_rw [Real.rpow_one]
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ c hc
    filter_upwards [eventually_ne_atTop 0] with n hn h
    exact absurd h (Nat.cast_ne_zero.mpr hn)
  have := LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun _ ↦ Nat.cast_nonneg _) zero_le_one
    (s := (s : ℂ)) (by simpa using hs)
  unfold LSeriesSummable at this
  have h2 := (funext (zetaReal_term_eq K (zero_lt_one.trans hs)))
  simp only [Complex.ofReal_natCast] at this h2
  rw [h2] at this
  exact Complex.summable_ofReal.mp this

theorem dedekindZeta_eq_zetaReal {s : ℝ} (hs : 1 < s) :
    dedekindZeta K (s : ℂ) = ((zetaReal K s : ℝ) : ℂ) := by
  unfold dedekindZeta LSeries zetaReal
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n ↦ zetaReal_term_eq K (zero_lt_one.trans hs) n

theorem sum_le_zetaReal {s : ℝ} (hs : 1 < s) (T : Finset (Ideal (𝓞 K))) :
    ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) ≤ zetaReal K s := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := Ideal.absNorm) (t := T.image Ideal.absNorm)
    (fun I hI ↦ Finset.mem_image_of_mem _ hI)]
  refine le_trans ?_ ((summable_zetaReal K hs).sum_le_tsum (T.image Ideal.absNorm)
    (fun n _ ↦ by positivity))
  refine Finset.sum_le_sum fun n _ ↦ ?_
  rw [Finset.sum_congr rfl (g := fun _ ↦ (n : ℝ) ^ (-s))
    (fun I hI ↦ by rw [(Finset.mem_filter.mp hI).2]), Finset.sum_const, nsmul_eq_mul]
  have hfin := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n
  have hc : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} = hfin.toFinset.card :=
    Nat.card_eq_card_finite_toFinset hfin
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [hc, Nat.cast_le]
  refine Finset.card_le_card fun I hI ↦ ?_
  simp only [Finset.mem_filter] at hI
  simpa using hI.2

theorem tendsto_zetaReal : Tendsto (zetaReal K) (𝓝[>] 1) atTop := by
  have h1 : Tendsto (fun s : ℝ ↦ (s - 1) * zetaReal K s) (𝓝[>] 1)
      (𝓝 (dedekindZeta_residue K)) := by
    have h := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
    refine (h.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    simp only [Function.comp_apply, dedekindZeta_eq_zetaReal K hs]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h2 : Tendsto (fun s : ℝ ↦ (s - 1)⁻¹) (𝓝[>] 1) atTop := by
    refine tendsto_inv_nhdsGT_zero.comp ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ ↦ s - 1) (𝓝 1) (𝓝 (1 - 1)) := tendsto_id.sub tendsto_const_nhds
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      exact sub_pos.mpr hs
  refine (h1.pos_mul_atTop (dedekindZeta_residue_pos K) h2).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs.ne'
  field_simp

theorem sum_le_prod_geom {s : ℝ} (hs : 0 < s) (T : Finset (Ideal (𝓞 K))) :
    ∃ P : Finset (HeightOneSpectrum (𝓞 K)), ∃ B : ℕ,
      ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) ≤
        ∏ v ∈ P, ∑ k ∈ Finset.range (B + 1), ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) ^ k := by
  classical
  set f : Ideal (𝓞 K) → ℝ := fun I ↦ (Ideal.absNorm I : ℝ) ^ (-s) with hf
  have hf0 : ∀ I, 0 ≤ f I := fun I ↦ by positivity
  set T' := T.filter (· ≠ ⊥) with hT'
  have hT'ne : ∀ I ∈ T', I ≠ 0 := fun I hI ↦ (Finset.mem_filter.mp hI).2
  have hsumT : ∑ I ∈ T, f I = ∑ I ∈ T', f I := by
    rw [hT', Finset.sum_filter_of_ne]
    intro I _ hI hbot
    apply hI
    simp [hf, hbot, Ideal.absNorm_bot, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
  have hS : (⋃ I ∈ (T' : Set (Ideal (𝓞 K))), {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ I}).Finite :=
    Set.Finite.biUnion T'.finite_toSet fun I hI ↦ Ideal.finite_factors (hT'ne I hI)
  set P := hS.toFinset with hP
  let cnt : HeightOneSpectrum (𝓞 K) → Ideal (𝓞 K) → ℕ := fun v I ↦
    (Associates.mk v.asIdeal).count (Associates.mk I).factors
  set B := T'.sup fun I ↦ P.sup fun v ↦ cnt v I with hB
  refine ⟨P, B, ?_⟩
  let g : (P → ℕ) → Ideal (𝓞 K) := fun e ↦ ∏ v : P, v.1.asIdeal ^ e v
  let t : P → Finset ℕ := fun _ ↦ Finset.range (B + 1)
  have hsub : T' ⊆ (Fintype.piFinset t).image g := by
    intro I hI
    refine Finset.mem_image.mpr ⟨fun v ↦ cnt v.1 I, ?_, ?_⟩
    · refine Fintype.mem_piFinset.mpr fun v ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
      exact le_trans (Finset.le_sup (f := fun v ↦ cnt v I) v.2)
        (Finset.le_sup (f := fun I ↦ P.sup fun v ↦ cnt v I) hI)
    · have hsupp : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) ↦ v.maxPowDividing I) ⊆
          (P : Set _) := by
        intro v hv
        rw [hP, Set.Finite.coe_toFinset]
        refine Set.mem_biUnion hI ?_
        by_contra hnd
        apply hv
        have h0 : cnt v I = 0 := by
          by_contra h
          exact hnd ((Associates.count_ne_zero_iff_dvd (hT'ne I hI) v.irreducible).mp h)
        simp only [HeightOneSpectrum.maxPowDividing]
        rw [show (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 from h0, pow_zero]
      have := Ideal.finprod_heightOneSpectrum_factorization (hT'ne I hI)
      rw [finprod_eq_prod_of_mulSupport_subset _ hsupp] at this
      exact (Finset.prod_coe_sort P (fun v ↦ v.maxPowDividing I)).trans this
  have hgf : ∀ e : P → ℕ, f (g e) = ∏ v : P, ((Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s)) ^ e v := by
    intro e
    simp only [hf, g, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
    rw [← Real.finsetProd_rpow _ _ (fun _ _ ↦ by positivity)]
    exact Finset.prod_congr rfl fun v _ ↦ (Real.rpow_pow_comm (Nat.cast_nonneg _) _ _).symm
  calc ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) = ∑ I ∈ T', f I := hsumT
    _ ≤ ∑ I ∈ (Fintype.piFinset t).image g, f I :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun I _ _ ↦ hf0 I
    _ ≤ ∑ e ∈ Fintype.piFinset t, f (g e) :=
        Finset.sum_image_le_of_nonneg fun I _ ↦ hf0 I
    _ = ∑ e ∈ Fintype.piFinset t, ∏ v : P, ((Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s)) ^ e v :=
        Finset.sum_congr rfl fun e _ ↦ hgf e
    _ = ∏ v : P, ∑ k ∈ t v, ((Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s)) ^ k :=
        (Finset.prod_univ_sum t _).symm
    _ = ∏ v ∈ P, ∑ k ∈ Finset.range (B + 1), ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) ^ k :=
        Finset.prod_coe_sort P (fun v ↦ ∑ k ∈ Finset.range (B + 1),
          ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) ^ k)

end DedekindZetaReal

open DedekindZetaReal

theorem summable_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
  classical
  refine summable_of_sum_le (c := zetaReal K s) (fun _ ↦ by positivity) fun u ↦ ?_
  rw [← Finset.sum_image (f := fun I : Ideal (𝓞 K) ↦ (Ideal.absNorm I : ℝ) ^ (-s))
    (g := HeightOneSpectrum.asIdeal) (fun v _ w _ h ↦ HeightOneSpectrum.ext h)]
  exact sum_le_zetaReal K hs _

namespace DedekindZetaReal

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast this

theorem geom_le_exp {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) (B : ℕ) :
    ∑ k ∈ Finset.range (B + 1), x ^ k ≤ Real.exp (2 * x) := by
  have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := B + 1) h0 (by linarith)
  rw [← Finset.range_eq_Ico, pow_zero] at hg
  have h2 : 1 / (1 - x) ≤ 1 + 2 * x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith [Real.add_one_le_exp (2 * x)]

theorem sum_le_exp {s : ℝ} (hs : 1 < s) (T : Finset (Ideal (𝓞 K))) :
    ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) ≤
      Real.exp (2 * ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
  obtain ⟨P, B, hPB⟩ := sum_le_prod_geom K (zero_lt_one.trans hs) T
  refine hPB.trans ?_
  have hx : ∀ v : HeightOneSpectrum (𝓞 K), (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) ≤ 1 / 2 := by
    intro v
    have h2 := two_le_absNorm K v
    calc (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 / (Ideal.absNorm v.asIdeal : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le two_pos h2
  calc ∏ v ∈ P, ∑ k ∈ Finset.range (B + 1), ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) ^ k
      ≤ ∏ v ∈ P, Real.exp (2 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) :=
        Finset.prod_le_prod (fun v _ ↦ Finset.sum_nonneg fun k _ ↦ by positivity)
          fun v _ ↦ geom_le_exp (by positivity) (hx v) B
    _ = Real.exp (2 * ∑ v ∈ P, (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) := by
        rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := by
        refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ two_pos.le)
        exact (summable_absNorm_rpow K hs).sum_le_tsum P fun _ _ ↦ by positivity

theorem sum_card_eq {s : ℝ} (u : Finset ℕ) :
    ∑ n ∈ u, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) =
      ∑ I ∈ u.biUnion (fun n ↦ (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).toFinset),
        (Ideal.absNorm I : ℝ) ^ (-s) := by
  classical
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun n _ ↦ ?_
    have hfin := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n
    have hc : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} = hfin.toFinset.card :=
      Nat.card_eq_card_finite_toFinset hfin
    rw [Finset.sum_congr rfl (g := fun _ ↦ (n : ℝ) ^ (-s)) (fun I hI ↦ by
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hI
      rw [hI]), Finset.sum_const, nsmul_eq_mul, hc]
  · intro n _ m _ hnm
    refine Finset.disjoint_left.mpr fun I h1 h2 ↦ hnm ?_
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at h1 h2
    exact h1.symm.trans h2

theorem zetaReal_le_exp {s : ℝ} (hs : 1 < s) :
    zetaReal K s ≤
      Real.exp (2 * ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
  refine Real.tsum_le_of_sum_le (fun n ↦ by positivity) fun u ↦ ?_
  rw [sum_card_eq]
  exact sum_le_exp K hs _

end DedekindZetaReal

theorem tendsto_primeIdealZetaSum_univ :
    Tendsto (fun s : ℝ => NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s) (𝓝[>] 1) atTop := by
  have h1 : Tendsto (fun s ↦ Real.log (zetaReal K s) / 2) (𝓝[>] 1) atTop :=
    (Real.tendsto_log_atTop.comp (tendsto_zetaReal K)).atTop_div_const two_pos
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [self_mem_nhdsWithin, (tendsto_zetaReal K).eventually_gt_atTop 0]
    with s (hs : 1 < s) hpos
  have e : (∑' 𝔭 : (Set.univ : Set (HeightOneSpectrum (𝓞 K))),
      (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) =
      ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) :=
    tsum_univ (fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))
  rw [NumberField.Set.primeIdealZetaSum_def, e]
  have := (Real.log_le_iff_le_exp hpos).mpr (zetaReal_le_exp K hs)
  linarith

end ReciprocityTheory.Neutral.Bridge
